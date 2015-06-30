// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify QuantifierVisibilityInvariant.dll

type real;

type elements;

type struct;

type exposeVersionType;

var $Heap: [ref,<x>name]x where IsHeap($Heap);

function IsHeap(h: [ref,<x>name]x) returns (bool);

const $allocated: <bool>name;

const $elements: <elements>name;

const $inv: <name>name;

const $localinv: <name>name;

const $exposeVersion: <exposeVersionType>name;

axiom DeclType($exposeVersion) == System.Object;

const $sharingMode: name;

const $SharingMode_Unshared: name;

const $SharingMode_LockProtected: name;

const $ownerRef: <ref>name;

const $ownerFrame: <name>name;

const $PeerGroupPlaceholder: name;

function ClassRepr(class: name) returns (ref);

axiom (forall c0: name, c1: name :: { ClassRepr(c0), ClassRepr(c1) } c0 != c1 ==> ClassRepr(c0) != ClassRepr(c1));

axiom (forall T: name :: !($typeof(ClassRepr(T)) <: System.Object));

axiom (forall T: name :: ClassRepr(T) != null);

axiom (forall T: name, h: [ref,<x>name]x :: { h[ClassRepr(T), $ownerFrame] } IsHeap(h) ==> h[ClassRepr(T), $ownerFrame] == $PeerGroupPlaceholder);

function IsDirectlyModifiableField(f: name) returns (bool);

axiom !IsDirectlyModifiableField($allocated);

axiom IsDirectlyModifiableField($elements);

axiom !IsDirectlyModifiableField($inv);

axiom !IsDirectlyModifiableField($localinv);

axiom !IsDirectlyModifiableField($ownerRef);

axiom !IsDirectlyModifiableField($ownerFrame);

axiom !IsDirectlyModifiableField($exposeVersion);

function IsStaticField(f: name) returns (bool);

axiom !IsStaticField($allocated);

axiom !IsStaticField($elements);

axiom !IsStaticField($inv);

axiom !IsStaticField($localinv);

axiom !IsStaticField($exposeVersion);

function ValueArrayGet(elements, int) returns (any);

function ValueArraySet(elements, int, any) returns (elements);

function RefArrayGet(elements, int) returns (ref);

function RefArraySet(elements, int, ref) returns (elements);

axiom (forall A: elements, i: int, x: any :: ValueArrayGet(ValueArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: any :: i != j ==> ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j));

axiom (forall A: elements, i: int, x: ref :: RefArrayGet(RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j));

function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);

axiom (forall a: ref, d: int, x: int, y: int, x': int, y': int :: { ArrayIndex(a, d, x, y), ArrayIndex(a, d, x', y') } ArrayIndex(a, d, x, y) == ArrayIndex(a, d, x', y') ==> x == x' && y == y');

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,<x>name]x :: { $typeof(a) <: RefArray(T, r), RefArrayGet(heap[a, $elements], i) } IsHeap(heap) && $typeof(a) <: RefArray(T, r) ==> $Is(RefArrayGet(heap[a, $elements], i), T));

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,<x>name]x :: { $typeof(a) <: NonNullRefArray(T, r), RefArrayGet(heap[a, $elements], i) } IsHeap(heap) && $typeof(a) <: NonNullRefArray(T, r) ==> $IsNotNull(RefArrayGet(heap[a, $elements], i), T));

function $Rank(ref) returns (int);

axiom (forall a: ref :: 1 <= $Rank(a));

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: RefArray(T, r) } a != null && $typeof(a) <: RefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: NonNullRefArray(T, r) } a != null && $typeof(a) <: NonNullRefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: ValueArray(T, r) } a != null && $typeof(a) <: ValueArray(T, r) ==> $Rank(a) == r);

function $Length(ref) returns (int);

axiom (forall a: ref :: { $Length(a) } 0 <= $Length(a));

function $DimLength(ref, int) returns (int);

axiom (forall a: ref, i: int :: 0 <= $DimLength(a, i));

axiom (forall a: ref :: { $DimLength(a, 0) } $Rank(a) == 1 ==> $DimLength(a, 0) == $Length(a));

function $LBound(ref, int) returns (int);

function $UBound(ref, int) returns (int);

axiom (forall a: ref, i: int :: { $LBound(a, i) } $LBound(a, i) == 0);

axiom (forall a: ref, i: int :: { $UBound(a, i) } $UBound(a, i) == $DimLength(a, i) - 1);

const $ArrayCategoryValue: name;

const $ArrayCategoryRef: name;

const $ArrayCategoryNonNullRef: name;

function $ArrayCategory(arrayType: name) returns (arrayCategory: name);

axiom (forall T: name, ET: name, r: int :: { T <: ValueArray(ET, r) } T <: ValueArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryValue);

axiom (forall T: name, ET: name, r: int :: { T <: RefArray(ET, r) } T <: RefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryRef);

axiom (forall T: name, ET: name, r: int :: { T <: NonNullRefArray(ET, r) } T <: NonNullRefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryNonNullRef);

const System.Array: name;

axiom System.Array <: System.Object;

function $ElementType(name) returns (name);

function ValueArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { ValueArray(T, r) } ValueArray(T, r) <: System.Array);

function RefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { RefArray(T, r) } RefArray(T, r) <: System.Array);

function NonNullRefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { NonNullRefArray(T, r) } NonNullRefArray(T, r) <: System.Array);

axiom (forall T: name, U: name, r: int :: U <: T ==> RefArray(U, r) <: RefArray(T, r));

axiom (forall T: name, U: name, r: int :: U <: T ==> NonNullRefArray(U, r) <: NonNullRefArray(T, r));

axiom (forall A: name, r: int :: $ElementType(ValueArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(RefArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(NonNullRefArray(A, r)) == A);

axiom (forall A: name, r: int, T: name :: { T <: RefArray(A, r) } T <: RefArray(A, r) ==> T == RefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: NonNullRefArray(A, r) } T <: NonNullRefArray(A, r) ==> T == NonNullRefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: ValueArray(A, r) } T <: ValueArray(A, r) ==> T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: RefArray(A, r) <: T ==> System.Array <: T || (T == RefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: NonNullRefArray(A, r) <: T ==> System.Array <: T || (T == NonNullRefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: ValueArray(A, r) <: T ==> System.Array <: T || T == ValueArray(A, r));

function $ArrayPtr(elementType: name) returns (name);

function $StructGet(struct, name) returns (any);

function $StructSet(struct, name, any) returns (struct);

axiom (forall s: struct, f: name, x: any :: $StructGet($StructSet(s, f, x), f) == x);

axiom (forall s: struct, f: name, f': name, x: any :: f != f' ==> $StructGet($StructSet(s, f, x), f') == $StructGet(s, f'));

function ZeroInit(s: struct, typ: name) returns (bool);

function $typeof(ref) returns (name);

function $BaseClass(sub: name) returns (base: name);

function AsDirectSubClass(sub: name, base: name) returns (sub': name);

function OneClassDown(sub: name, base: name) returns (directSub: name);

axiom (forall A: name, B: name, C: name :: { C <: AsDirectSubClass(B, A) } C <: AsDirectSubClass(B, A) ==> OneClassDown(C, A) == B);

function $IsValueType(name) returns (bool);

axiom (forall T: name :: $IsValueType(T) ==> (forall U: name :: T <: U ==> T == U) && (forall U: name :: U <: T ==> T == U));

const System.Object: name;

function $IsTokenForType(struct, name) returns (bool);

function TypeObject(name) returns (ref);

const System.Type: name;

axiom System.Type <: System.Object;

axiom (forall T: name :: { TypeObject(T) } $IsNotNull(TypeObject(T), System.Type));

function TypeName(ref) returns (name);

axiom (forall T: name :: { TypeObject(T) } TypeName(TypeObject(T)) == T);

function $Is(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $Is(o, T) } $Is(o, T) <==> o == null || $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $IsNotNull(o, T) } $IsNotNull(o, T) <==> o != null && $Is(o, T));

function $As(ref, name) returns (ref);

axiom (forall o: ref, T: name :: $Is(o, T) ==> $As(o, T) == o);

axiom (forall o: ref, T: name :: !$Is(o, T) ==> $As(o, T) == null);

axiom (forall h: [ref,<x>name]x, o: ref :: { $typeof(o) <: System.Array, h[o, $inv] } IsHeap(h) && o != null && $typeof(o) <: System.Array ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

function IsAllocated(h: [ref,<x>name]x, o: any) returns (bool);

axiom (forall h: [ref,<x>name]x, o: ref, f: name :: { IsAllocated(h, h[o, f]) } IsHeap(h) && h[o, $allocated] ==> IsAllocated(h, h[o, f]));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[h[o, f], $allocated] } IsHeap(h) && h[o, $allocated] ==> h[h[o, f], $allocated]);

axiom (forall h: [ref,<x>name]x, s: struct, f: name :: { IsAllocated(h, $StructGet(s, f)) } IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, RefArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, ValueArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, ValueArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, o: ref :: { h[o, $allocated] } IsAllocated(h, o) ==> h[o, $allocated]);

axiom (forall h: [ref,<x>name]x, c: name :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> h[ClassRepr(c), $allocated]);

const $BeingConstructed: ref;

const $NonNullFieldsAreInitialized: <bool>name;

function DeclType(field: name) returns (class: name);

function AsNonNullRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRangeField(field: <int>name, T: name) returns (f: <int>name);

axiom (forall f: <ref>name, T: name :: { AsNonNullRefField(f, T) } AsNonNullRefField(f, T) == f ==> AsRefField(f, T) == f);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRefField(f, T)] } IsHeap(h) ==> $Is(h[o, AsRefField(f, T)], T));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsNonNullRefField(f, T)] } IsHeap(h) && o != null && (o != $BeingConstructed || h[$BeingConstructed, $NonNullFieldsAreInitialized] == true) ==> h[o, AsNonNullRefField(f, T)] != null);

axiom (forall h: [ref,<x>name]x, o: ref, f: <int>name, T: name :: { h[o, AsRangeField(f, T)] } IsHeap(h) ==> InRange(h[o, AsRangeField(f, T)], T));

function $IsMemberlessType(name) returns (bool);

axiom (forall o: ref :: { $IsMemberlessType($typeof(o)) } !$IsMemberlessType($typeof(o)));

function $IsImmutable(T: name) returns (bool);

axiom !$IsImmutable(System.Object);

function $AsImmutable(T: name) returns (theType: name);

function $AsMutable(T: name) returns (theType: name);

axiom (forall T: name, U: name :: { U <: $AsImmutable(T) } U <: $AsImmutable(T) ==> $IsImmutable(U) && $AsImmutable(U) == U);

axiom (forall T: name, U: name :: { U <: $AsMutable(T) } U <: $AsMutable(T) ==> !$IsImmutable(U) && $AsMutable(U) == U);

function AsOwner(string: ref, owner: ref) returns (theString: ref);

axiom (forall o: ref, T: name :: { $typeof(o) <: $AsImmutable(T) } o != null && o != $BeingConstructed && $typeof(o) <: $AsImmutable(T) ==> (forall h: [ref,<x>name]x :: { IsHeap(h) } IsHeap(h) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o) && h[o, $ownerFrame] == $PeerGroupPlaceholder && AsOwner(o, h[o, $ownerRef]) == o && (forall t: ref :: { AsOwner(o, h[t, $ownerRef]) } AsOwner(o, h[t, $ownerRef]) == o ==> t == o || h[t, $ownerFrame] != $PeerGroupPlaceholder)));

const System.String: name;

function $StringLength(ref) returns (int);

axiom (forall s: ref :: { $StringLength(s) } 0 <= $StringLength(s));

function AsRepField(f: <ref>name, declaringType: name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRepField(f, T)] } IsHeap(h) && h[o, AsRepField(f, T)] != null ==> h[h[o, AsRepField(f, T)], $ownerRef] == o && h[h[o, AsRepField(f, T)], $ownerFrame] == T);

function AsPeerField(f: <ref>name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[o, AsPeerField(f)] } IsHeap(h) && h[o, AsPeerField(f)] != null ==> h[h[o, AsPeerField(f)], $ownerRef] == h[o, $ownerRef] && h[h[o, AsPeerField(f)], $ownerFrame] == h[o, $ownerFrame]);

axiom (forall h: [ref,<x>name]x, o: ref :: { h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] } IsHeap(h) && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

procedure $SetOwner(o: ref, ow: ref, fr: name);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[o, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[o, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[o, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[o, $ownerFrame]) ==> $Heap[p, $ownerRef] == ow && $Heap[p, $ownerFrame] == fr);



procedure $UpdateOwnersForRep(o: ref, T: name, e: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[e, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[e, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures e == null ==> $Heap == old($Heap);
  ensures e != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[e, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[e, $ownerFrame]) ==> $Heap[p, $ownerRef] == o && $Heap[p, $ownerFrame] == T);



procedure $UpdateOwnersForPeer(c: ref, d: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old(($Heap[p, $ownerRef] != $Heap[c, $ownerRef] || $Heap[p, $ownerFrame] != $Heap[c, $ownerFrame]) && ($Heap[p, $ownerRef] != $Heap[d, $ownerRef] || $Heap[p, $ownerFrame] != $Heap[d, $ownerFrame])) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures d == null ==> $Heap == old($Heap);
  ensures d != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } (old($Heap[p, $ownerRef] == $Heap[c, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[c, $ownerFrame])) || (old($Heap[p, $ownerRef] == $Heap[d, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[d, $ownerFrame])) ==> (old($Heap)[d, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerRef] == old($Heap)[c, $ownerRef] && $Heap[p, $ownerFrame] == old($Heap)[c, $ownerFrame]) || (old($Heap)[d, $ownerFrame] != $PeerGroupPlaceholder && $Heap[p, $ownerRef] == old($Heap)[d, $ownerRef] && $Heap[p, $ownerFrame] == old($Heap)[d, $ownerFrame]));



const $FirstConsistentOwner: <ref>name;

function $AsPureObject(ref) returns (ref);

function ##FieldDependsOnFCO(o: ref, f: name, ev: exposeVersionType) returns (value: any);

axiom (forall o: ref, f: name, h: [ref,<x>name]x :: { h[$AsPureObject(o), f] } IsHeap(h) && o != null && h[o, $allocated] == true && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, f] == ##FieldDependsOnFCO(o, f, h[h[o, $FirstConsistentOwner], $exposeVersion]));

axiom (forall o: ref, h: [ref,<x>name]x :: { h[o, $FirstConsistentOwner] } IsHeap(h) && o != null && h[o, $allocated] == true && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $FirstConsistentOwner] != null && h[h[o, $FirstConsistentOwner], $allocated] == true && (h[h[o, $FirstConsistentOwner], $ownerFrame] == $PeerGroupPlaceholder || !(h[h[h[o, $FirstConsistentOwner], $ownerRef], $inv] <: h[h[o, $FirstConsistentOwner], $ownerFrame]) || h[h[h[o, $FirstConsistentOwner], $ownerRef], $localinv] == $BaseClass(h[h[o, $FirstConsistentOwner], $ownerFrame])));

function Box(any, ref) returns (ref);

function Unbox(ref) returns (any);

axiom (forall x: any, p: ref :: { Unbox(Box(x, p)) } Unbox(Box(x, p)) == x);

function UnboxedType(ref) returns (name);

axiom (forall p: ref :: { $IsValueType(UnboxedType(p)) } $IsValueType(UnboxedType(p)) ==> (forall heap: [ref,<x>name]x, x: any :: { heap[Box(x, p), $inv] } IsHeap(heap) ==> heap[Box(x, p), $inv] == $typeof(Box(x, p)) && heap[Box(x, p), $localinv] == $typeof(Box(x, p))));

axiom (forall x: any, p: ref :: { UnboxedType(Box(x, p)) <: System.Object } UnboxedType(Box(x, p)) <: System.Object && Box(x, p) == p ==> x == p);

function BoxTester(p: ref, typ: name) returns (ref);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } UnboxedType(p) == typ <==> BoxTester(p, typ) != null);

const System.SByte: name;

axiom $IsValueType(System.SByte);

const System.Byte: name;

axiom $IsValueType(System.Byte);

const System.Int16: name;

axiom $IsValueType(System.Int16);

const System.UInt16: name;

axiom $IsValueType(System.UInt16);

const System.Int32: name;

axiom $IsValueType(System.Int32);

const System.UInt32: name;

axiom $IsValueType(System.UInt32);

const System.Int64: name;

axiom $IsValueType(System.Int64);

const System.UInt64: name;

axiom $IsValueType(System.UInt64);

const System.Char: name;

axiom $IsValueType(System.Char);

const int#m2147483648: int;

const int#2147483647: int;

const int#4294967295: int;

const int#m9223372036854775808: int;

const int#9223372036854775807: int;

const int#18446744073709551615: int;

axiom int#m9223372036854775808 < int#m2147483648;

axiom int#m2147483648 < 0 - 100000;

axiom 100000 < int#2147483647;

axiom int#2147483647 < int#4294967295;

axiom int#4294967295 < int#9223372036854775807;

axiom int#9223372036854775807 < int#18446744073709551615;

function InRange(i: int, T: name) returns (bool);

axiom (forall i: int :: InRange(i, System.SByte) <==> 0 - 128 <= i && i < 128);

axiom (forall i: int :: InRange(i, System.Byte) <==> 0 <= i && i < 256);

axiom (forall i: int :: InRange(i, System.Int16) <==> 0 - 32768 <= i && i < 32768);

axiom (forall i: int :: InRange(i, System.UInt16) <==> 0 <= i && i < 65536);

axiom (forall i: int :: InRange(i, System.Int32) <==> int#m2147483648 <= i && i <= int#2147483647);

axiom (forall i: int :: InRange(i, System.UInt32) <==> 0 <= i && i <= int#4294967295);

axiom (forall i: int :: InRange(i, System.Int64) <==> int#m9223372036854775808 <= i && i <= int#9223372036854775807);

axiom (forall i: int :: InRange(i, System.UInt64) <==> 0 <= i && i <= int#18446744073709551615);

axiom (forall i: int :: InRange(i, System.Char) <==> 0 <= i && i < 65536);

function $IntToInt(val: int, fromType: name, toType: name) returns (int);

function $IntToReal(int, fromType: name, toType: name) returns (real);

function $RealToInt(real, fromType: name, toType: name) returns (int);

function $RealToReal(val: real, fromType: name, toType: name) returns (real);

function $SizeIs(name, int) returns (bool);

function $IfThenElse(bool, any, any) returns (any);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } b ==> $IfThenElse(b, x, y) == x);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } !b ==> $IfThenElse(b, x, y) == y);

function #neg(int) returns (int);

function #and(int, int) returns (int);

function #or(int, int) returns (int);

function #xor(int, int) returns (int);

function #shl(int, int) returns (int);

function #shr(int, int) returns (int);

function #rneg(real) returns (real);

function #radd(real, real) returns (real);

function #rsub(real, real) returns (real);

function #rmul(real, real) returns (real);

function #rdiv(real, real) returns (real);

function #rmod(real, real) returns (real);

function #rLess(real, real) returns (bool);

function #rAtmost(real, real) returns (bool);

function #rEq(real, real) returns (bool);

function #rNeq(real, real) returns (bool);

function #rAtleast(real, real) returns (bool);

function #rGreater(real, real) returns (bool);

axiom (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);

axiom (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);

axiom (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);

axiom (forall x: int, y: int :: { (x - y) % y } 0 <= x - y && 0 <= y ==> (x - y) % y == x % y);

axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b ==> a + d <= b);

axiom (forall x: int, y: int :: { #and(x, y) } 0 <= x || 0 <= y ==> 0 <= #and(x, y));

axiom (forall x: int, y: int :: { #or(x, y) } 0 <= x && 0 <= y ==> 0 <= #or(x, y) && #or(x, y) <= x + y);

axiom (forall i: int :: { #shl(i, 0) } #shl(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shl(i, j + 1) == #shl(i, j) * 2);

axiom (forall i: int :: { #shr(i, 0) } #shr(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shr(i, j + 1) == #shr(i, j) / 2);

function #System.String.IsInterned$System.String$notnull(ref) returns (ref);

function #System.String.Equals$System.String(ref, ref) returns (bool);

function #System.String.Equals$System.String$System.String(ref, ref) returns (bool);

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String(a, b) } #System.String.Equals$System.String(a, b) == #System.String.Equals$System.String$System.String(a, b));

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String$System.String(a, b) } #System.String.Equals$System.String$System.String(a, b) == #System.String.Equals$System.String$System.String(b, a));

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String$System.String(a, b) } a != null && b != null && #System.String.Equals$System.String$System.String(a, b) ==> #System.String.IsInterned$System.String$notnull(a) == #System.String.IsInterned$System.String$notnull(b));

const $UnknownRef: ref;

const A.y: <int>name;

const B.others: <ref>name;

const AbstractCity0.a0: <ref>name;

const C.others: <ref>name;

const A.x: <int>name;

const A.others: <ref>name;

const AnotherInvariantNameIssue.x: <int>name;

const A.z: <int>name;

const AbstractCity1.a1: <ref>name;

const System.Runtime.InteropServices._Exception: name;

const AbstractCity1: name;

const Microsoft.Contracts.GuardException: name;

const B: name;

const System.Boolean: name;

const Microsoft.Contracts.ICheckedException: name;

const AbstractCity0: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.Reflection.MemberInfo: name;

const System.Runtime.Serialization.ISerializable: name;

const A: name;

const System.Reflection.IReflect: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Exception: name;

const System.Runtime.InteropServices._Type: name;

const C: name;

const AnotherInvariantNameIssue: name;

const System.Reflection.ICustomAttributeProvider: name;

axiom !IsStaticField(A.others);

axiom IsDirectlyModifiableField(A.others);

axiom AsRepField(A.others, A) == A.others;

axiom DeclType(A.others) == A;

axiom AsNonNullRefField(A.others, RefArray(A, 1)) == A.others;

axiom !IsStaticField(A.x);

axiom IsDirectlyModifiableField(A.x);

axiom DeclType(A.x) == A;

axiom AsRangeField(A.x, System.Int32) == A.x;

axiom !IsStaticField(A.y);

axiom IsDirectlyModifiableField(A.y);

axiom DeclType(A.y) == A;

axiom AsRangeField(A.y, System.Int32) == A.y;

axiom !IsStaticField(A.z);

axiom IsDirectlyModifiableField(A.z);

axiom DeclType(A.z) == A;

axiom AsRangeField(A.z, System.Int32) == A.z;

axiom !IsStaticField(AbstractCity0.a0);

axiom IsDirectlyModifiableField(AbstractCity0.a0);

axiom DeclType(AbstractCity0.a0) == AbstractCity0;

axiom AsRefField(AbstractCity0.a0, A) == AbstractCity0.a0;

axiom !IsStaticField(B.others);

axiom IsDirectlyModifiableField(B.others);

axiom AsRepField(B.others, B) == B.others;

axiom DeclType(B.others) == B;

axiom AsNonNullRefField(B.others, RefArray(System.Object, 1)) == B.others;

axiom !IsStaticField(AbstractCity1.a1);

axiom IsDirectlyModifiableField(AbstractCity1.a1);

axiom DeclType(AbstractCity1.a1) == AbstractCity1;

axiom AsRefField(AbstractCity1.a1, A) == AbstractCity1.a1;

axiom !IsStaticField(C.others);

axiom IsDirectlyModifiableField(C.others);

axiom AsRepField(C.others, C) == C.others;

axiom DeclType(C.others) == C;

axiom AsNonNullRefField(C.others, RefArray(System.Object, 1)) == C.others;

axiom !IsStaticField(AnotherInvariantNameIssue.x);

axiom IsDirectlyModifiableField(AnotherInvariantNameIssue.x);

axiom DeclType(AnotherInvariantNameIssue.x) == AnotherInvariantNameIssue;

axiom AsRangeField(AnotherInvariantNameIssue.x, System.Int32) == AnotherInvariantNameIssue.x;

axiom A <: A;

axiom $BaseClass(A) == System.Object;

axiom A <: $BaseClass(A) && AsDirectSubClass(A, $BaseClass(A)) == A;

axiom !$IsImmutable(A) && $AsMutable(A) == A;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: A } IsHeap($h) && $h[$oi, $inv] <: A && $h[$oi, $localinv] != System.Object ==> (forall ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($h[$oi, A.others]) - 1 ==> ^ijk % 2 == 0 ==> RefArrayGet($h[$h[$oi, A.others], $elements], ^ijk) != null ==> $h[RefArrayGet($h[$h[$oi, A.others], $elements], ^ijk), A.x] == 7));

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure A.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, local0: bool where true, local1: int where InRange(local1, System.Int32), stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, local2: bool where true, stack1o: ref, SS$Display.Return.Local: bool where true, stack50000o: ref, $Heap$block3094$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block3060;

  block3060:
    goto block3077;

  block3077:
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(7,3)
    local0 := true;
    // ----- load constant 0
    local1 := 0;
    goto block3094$LoopPreheader;

  block3094:
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: $Heap$block3094$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block3094$LoopPreheader[$ot, $allocated] == true && $Heap$block3094$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block3094$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block3094$LoopPreheader[$ot, $ownerFrame]) && $Heap$block3094$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field
    assume (forall $o: ref :: ($Heap$block3094$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block3094$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block3094$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block3094$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields
    assert (forall $o: ref :: $o != null && $Heap$block3094$LoopPreheader[$o, $allocated] == true ==> $Heap$block3094$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block3094$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, A.others];
    // ----- array length
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true3094to3298, false3094to3111;

  true3094to3298:
    assume local1 > stack0i;
    goto block3298;

  false3094to3111:
    assume local1 <= stack0i;
    goto block3111;

  block3298:
    // ----- copy
    // ----- branch
    goto true3298to3400, false3298to3315;

  block3111:
    // ----- load constant 2
    stack0i := 2;
    // ----- binary operator
    assert stack0i != 0;
    stack0i := local1 % stack0i;
    // ----- load constant 0
    stack1i := 0;
    // ----- binary operator
    // ----- branch
    goto true3111to3247, false3111to3128;

  true3298to3400:
    assume local0;
    goto block3400;

  false3298to3315:
    assume !local0;
    goto block3315;

  block3400:
    // ----- load constant 1
    local2 := true;
    // ----- branch
    goto block3417;

  block3315:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true3315to3366, false3315to3332;

  true3111to3247:
    assume stack0i != stack1i;
    goto block3247;

  false3111to3128:
    assume stack0i == stack1i;
    goto block3128;

  block3247:
    // ----- copy
    // ----- branch
    goto true3247to3281, false3247to3264;

  block3128:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, A.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    stack1o := null;
    // ----- binary operator
    // ----- branch
    goto true3128to3213, false3128to3145;

  true3315to3366:
    assume !stack0b;
    goto block3366;

  false3315to3332:
    assume stack0b;
    goto block3332;

  block3366:
    // ----- load constant 0
    local2 := false;
    // ----- branch
    goto block3417;

  block3332:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  true3247to3281:
    assume local0;
    goto block3281;

  false3247to3264:
    assume !local0;
    goto block3264;

  block3281:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    local1 := stack0i;
    // ----- branch
    goto block3094;

  block3264:
    // ----- branch
    goto block3298;

  true3128to3213:
    assume stack0o == stack1o;
    goto block3213;

  false3128to3145:
    assume stack0o != stack1o;
    goto block3145;

  block3213:
    // ----- load constant 1
    stack0b := true;
    goto block3230;

  block3145:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, A.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- load field
    assert stack0o != null;
    stack0i := $Heap[stack0o, A.x];
    // ----- load constant 7
    stack1i := 7;
    // ----- binary operator
    // ----- branch
    goto true3145to3179, false3145to3162;

  block3417:
    // ----- copy
    SS$Display.Return.Local := local2;
    // ----- copy
    stack0b := local2;
    // ----- return
    $result := stack0b;
    return;

  true3145to3179:
    assume stack0i == stack1i;
    goto block3179;

  false3145to3162:
    assume stack0i != stack1i;
    goto block3162;

  block3179:
    // ----- load constant 1
    stack0b := true;
    goto block3196;

  block3162:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3196;

  block3230:
    // ----- copy
    local0 := stack0b;
    goto block3247;

  block3196:
    // ----- branch
    goto block3230;

  block3094$LoopPreheader:
    $Heap$block3094$LoopPreheader := $Heap;
    goto block3094;

}



axiom Microsoft.Contracts.ObjectInvariantException <: Microsoft.Contracts.ObjectInvariantException;

axiom Microsoft.Contracts.GuardException <: Microsoft.Contracts.GuardException;

axiom System.Exception <: System.Exception;

axiom $BaseClass(System.Exception) == System.Object;

axiom System.Exception <: $BaseClass(System.Exception) && AsDirectSubClass(System.Exception, $BaseClass(System.Exception)) == System.Exception;

axiom !$IsImmutable(System.Exception) && $AsMutable(System.Exception) == System.Exception;

axiom System.Runtime.Serialization.ISerializable <: System.Object;

axiom $IsMemberlessType(System.Runtime.Serialization.ISerializable);

axiom System.Exception <: System.Runtime.Serialization.ISerializable;

axiom System.Runtime.InteropServices._Exception <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Exception);

axiom System.Exception <: System.Runtime.InteropServices._Exception;

axiom $BaseClass(Microsoft.Contracts.GuardException) == System.Exception;

axiom Microsoft.Contracts.GuardException <: $BaseClass(Microsoft.Contracts.GuardException) && AsDirectSubClass(Microsoft.Contracts.GuardException, $BaseClass(Microsoft.Contracts.GuardException)) == Microsoft.Contracts.GuardException;

axiom !$IsImmutable(Microsoft.Contracts.GuardException) && $AsMutable(Microsoft.Contracts.GuardException) == Microsoft.Contracts.GuardException;

axiom $BaseClass(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.GuardException;

axiom Microsoft.Contracts.ObjectInvariantException <: $BaseClass(Microsoft.Contracts.ObjectInvariantException) && AsDirectSubClass(Microsoft.Contracts.ObjectInvariantException, $BaseClass(Microsoft.Contracts.ObjectInvariantException)) == Microsoft.Contracts.ObjectInvariantException;

axiom !$IsImmutable(Microsoft.Contracts.ObjectInvariantException) && $AsMutable(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.ObjectInvariantException;

procedure Microsoft.Contracts.ObjectInvariantException..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Microsoft.Contracts.ObjectInvariantException && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Microsoft.Contracts.ObjectInvariantException <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure A..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == A && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(A <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A..ctor(this: ref)
{
  var stack0i: int, stack0o: ref, temp0: ref;

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, A.x] == 0;
    assume $Heap[this, A.y] == 0;
    assume $Heap[this, A.z] == 0;
    goto block4505;

  block4505:
    goto block4522;

  block4522:
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(9,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block4590;

  block4590:
    // ----- load constant 10  ----- QuantifierVisibilityInvariant.ssc(10,5)
    stack0i := 10;
    // ----- new array  ----- QuantifierVisibilityInvariant.ssc(10,5)
    assert 0 <= stack0i;
    havoc stack0o;
    assume $Heap[stack0o, $allocated] == false && $Length(stack0o) == stack0i;
    assume $IsNotNull(stack0o, RefArray(A, 1));
    assume $Heap[stack0o, $ownerRef] == stack0o && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[stack0o, $inv] == RefArray(A, 1) && $Heap[stack0o, $localinv] == RefArray(A, 1) && ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]));
    assume (forall $i: int :: RefArrayGet($Heap[stack0o, $elements], $i) == null);
    $Heap[stack0o, $allocated] := true;
    assume IsHeap($Heap);
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(10,5)
    assert this != null;
    assert !($Heap[this, $inv] <: A) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == A);
    $Heap[this, A.others] := stack0o;
    call $UpdateOwnersForRep(this, A, stack0o);
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(11,3)
    temp0 := this;
    // ----- classic pack  ----- QuantifierVisibilityInvariant.ssc(11,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert (forall ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($Heap[temp0, A.others]) - 1 ==> ^ijk % 2 == 0 ==> RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk) != null ==> $Heap[RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk), A.x] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == A ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := A;
    assume IsHeap($Heap);
    // ----- return  ----- QuantifierVisibilityInvariant.ssc(11,3)
    return;

}



procedure System.Object..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(System.Object <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure A.M(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A.M(this: ref)
{
  var ijk: int where InRange(ijk, System.Int32), local2: int where InRange(local2, System.Int32), stack0i: int, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local4: ref where $Is(local4, System.Exception), local5: int where InRange(local5, System.Int32), stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    goto block5457;

  block5457:
    goto block5610;

  block5610:
    // ----- nop
    // ----- load constant 0  ----- QuantifierVisibilityInvariant.ssc(14,5)
    ijk := 0;
    // ----- copy  ----- QuantifierVisibilityInvariant.ssc(15,5)
    local2 := ijk;
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(15,5)
    stack0i := 1;
    // ----- binary operator  ----- QuantifierVisibilityInvariant.ssc(15,5)
    stack0i := local2 + stack0i;
    // ----- copy  ----- QuantifierVisibilityInvariant.ssc(15,5)
    ijk := stack0i;
    // ----- copy
    stack0i := local2;
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(16,13)
    temp0 := this;
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(16,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(16,13)
    stack1o := TypeObject(A);
    // ----- local unpack  ----- QuantifierVisibilityInvariant.ssc(16,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: A && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local4 := null;
    goto block5627;

  block5627:
    // ----- load field  ----- QuantifierVisibilityInvariant.ssc(17,7)
    assert this != null;
    local5 := $Heap[this, A.x];
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(17,7)
    stack0i := 1;
    // ----- binary operator  ----- QuantifierVisibilityInvariant.ssc(17,7)
    stack0i := local5 + stack0i;
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(17,7)
    assert this != null;
    assert !($Heap[this, $inv] <: A) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref, ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($Heap[this, A.others]) - 1 ==> ^ijk % 2 == 0 ==> $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: A && RefArrayGet($Heap[$Heap[$o, A.others], $elements], ^ijk) == this ==> !($Heap[$o, $inv] <: A) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, A.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block5712;

  block5712:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true5712to5780, false5712to5729;

  true5712to5780:
    assume local4 == stack0o;
    goto block5780;

  false5712to5729:
    assume local4 != stack0o;
    goto block5729;

  block5780:
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(18,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(18,5)
    stack0o := TypeObject(A);
    // ----- local pack  ----- QuantifierVisibilityInvariant.ssc(18,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert (forall ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($Heap[temp0, A.others]) - 1 ==> ^ijk % 2 == 0 ==> RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk) != null ==> $Heap[RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk), A.x] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == A ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block5763;

  block5729:
    // ----- is instance
    // ----- branch
    goto true5729to5780, false5729to5746;

  true5729to5780:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block5780;

  false5729to5746:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block5746;

  block5746:
    // ----- branch
    goto block5763;

  block5763:
    // ----- nop
    // ----- branch
    goto block5678;

  block5678:
    // ----- return
    return;

}



axiom System.Type <: System.Type;

axiom System.Reflection.MemberInfo <: System.Reflection.MemberInfo;

axiom $BaseClass(System.Reflection.MemberInfo) == System.Object;

axiom System.Reflection.MemberInfo <: $BaseClass(System.Reflection.MemberInfo) && AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo;

axiom $IsImmutable(System.Reflection.MemberInfo) && $AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo;

axiom System.Reflection.ICustomAttributeProvider <: System.Object;

axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);

axiom System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider;

axiom System.Runtime.InteropServices._MemberInfo <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);

axiom System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo;

axiom $IsMemberlessType(System.Reflection.MemberInfo);

axiom $BaseClass(System.Type) == System.Reflection.MemberInfo;

axiom System.Type <: $BaseClass(System.Type) && AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type;

axiom $IsImmutable(System.Type) && $AsImmutable(System.Type) == System.Type;

axiom System.Runtime.InteropServices._Type <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Type);

axiom System.Type <: System.Runtime.InteropServices._Type;

axiom System.Reflection.IReflect <: System.Object;

axiom $IsMemberlessType(System.Reflection.IReflect);

axiom System.Type <: System.Reflection.IReflect;

axiom $IsMemberlessType(System.Type);

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure A.N(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A.N(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    goto block6987;

  block6987:
    goto block7140;

  block7140:
    // ----- nop
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(22,13)
    temp0 := this;
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(22,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(22,13)
    stack1o := TypeObject(A);
    // ----- local unpack  ----- QuantifierVisibilityInvariant.ssc(22,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: A && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block7157;

  block7157:
    // ----- load field  ----- QuantifierVisibilityInvariant.ssc(23,7)
    assert this != null;
    local3 := $Heap[this, A.y];
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(23,7)
    stack0i := 1;
    // ----- binary operator  ----- QuantifierVisibilityInvariant.ssc(23,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(23,7)
    assert this != null;
    assert !($Heap[this, $inv] <: A) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref, ^i: int :: 0 <= ^i && ^i <= $Length($Heap[this, B.others]) - 1 ==> $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: B && $Heap[RefArrayGet($Heap[$Heap[$o, B.others], $elements], ^i), AbstractCity0.a0] == this ==> !($Heap[$o, $inv] <: B) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, A.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block7242;

  block7242:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true7242to7310, false7242to7259;

  true7242to7310:
    assume local2 == stack0o;
    goto block7310;

  false7242to7259:
    assume local2 != stack0o;
    goto block7259;

  block7310:
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(24,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(24,5)
    stack0o := TypeObject(A);
    // ----- local pack  ----- QuantifierVisibilityInvariant.ssc(24,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert (forall ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($Heap[temp0, A.others]) - 1 ==> ^ijk % 2 == 0 ==> RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk) != null ==> $Heap[RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk), A.x] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == A ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block7293;

  block7259:
    // ----- is instance
    // ----- branch
    goto true7259to7310, false7259to7276;

  true7259to7310:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block7310;

  false7259to7276:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block7276;

  block7276:
    // ----- branch
    goto block7293;

  block7293:
    // ----- nop
    // ----- branch
    goto block7208;

  block7208:
    // ----- return
    return;

}



axiom AbstractCity0 <: AbstractCity0;

axiom $BaseClass(AbstractCity0) == System.Object;

axiom AbstractCity0 <: $BaseClass(AbstractCity0) && AsDirectSubClass(AbstractCity0, $BaseClass(AbstractCity0)) == AbstractCity0;

axiom !$IsImmutable(AbstractCity0) && $AsMutable(AbstractCity0) == AbstractCity0;

axiom $IsMemberlessType(AbstractCity0);

axiom (forall $U: name :: { $U <: AbstractCity0 } $U <: AbstractCity0 ==> $U == AbstractCity0);

axiom B <: B;

axiom $BaseClass(B) == System.Object;

axiom B <: $BaseClass(B) && AsDirectSubClass(B, $BaseClass(B)) == B;

axiom !$IsImmutable(B) && $AsMutable(B) == B;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: B } IsHeap($h) && $h[$oi, $inv] <: B && $h[$oi, $localinv] != System.Object ==> (forall ^i: int :: 0 <= ^i && ^i <= $Length($h[$oi, B.others]) - 1 ==> $IsNotNull(RefArrayGet($h[$h[$oi, B.others], $elements], ^i), AbstractCity0) && $h[RefArrayGet($h[$h[$oi, B.others], $elements], ^i), AbstractCity0.a0] != null ==> $h[$h[RefArrayGet($h[$h[$oi, B.others], $elements], ^i), AbstractCity0.a0], A.y] == 7));

procedure A.P(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A.P(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    goto block8415;

  block8415:
    goto block8568;

  block8568:
    // ----- nop
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(28,13)
    temp0 := this;
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(28,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(28,13)
    stack1o := TypeObject(A);
    // ----- local unpack  ----- QuantifierVisibilityInvariant.ssc(28,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: A && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block8585;

  block8585:
    // ----- load field  ----- QuantifierVisibilityInvariant.ssc(29,7)
    assert this != null;
    local3 := $Heap[this, A.z];
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(29,7)
    stack0i := 1;
    // ----- binary operator  ----- QuantifierVisibilityInvariant.ssc(29,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(29,7)
    assert this != null;
    assert !($Heap[this, $inv] <: A) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref, ^i: int :: 0 <= ^i && ^i <= $Length($Heap[this, C.others]) - 1 ==> $IsNotNull(RefArrayGet($Heap[$Heap[this, C.others], $elements], ^i), AbstractCity1) ==> $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: C && $Heap[RefArrayGet($Heap[$Heap[$o, C.others], $elements], ^i), AbstractCity1.a1] == this ==> !($Heap[$o, $inv] <: C) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, A.z] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block8670;

  block8670:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true8670to8738, false8670to8687;

  true8670to8738:
    assume local2 == stack0o;
    goto block8738;

  false8670to8687:
    assume local2 != stack0o;
    goto block8687;

  block8738:
    // ----- load token  ----- QuantifierVisibilityInvariant.ssc(30,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, A);
    // ----- statically resolved GetTypeFromHandle call  ----- QuantifierVisibilityInvariant.ssc(30,5)
    stack0o := TypeObject(A);
    // ----- local pack  ----- QuantifierVisibilityInvariant.ssc(30,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert (forall ^ijk: int :: 0 <= ^ijk && ^ijk <= $Length($Heap[temp0, A.others]) - 1 ==> ^ijk % 2 == 0 ==> RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk) != null ==> $Heap[RefArrayGet($Heap[$Heap[temp0, A.others], $elements], ^ijk), A.x] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == A ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block8721;

  block8687:
    // ----- is instance
    // ----- branch
    goto true8687to8738, false8687to8704;

  true8687to8738:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block8738;

  false8687to8704:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block8704;

  block8704:
    // ----- branch
    goto block8721;

  block8721:
    // ----- nop
    // ----- branch
    goto block8636;

  block8636:
    // ----- return
    return;

}



axiom AbstractCity1 <: AbstractCity1;

axiom $BaseClass(AbstractCity1) == System.Object;

axiom AbstractCity1 <: $BaseClass(AbstractCity1) && AsDirectSubClass(AbstractCity1, $BaseClass(AbstractCity1)) == AbstractCity1;

axiom !$IsImmutable(AbstractCity1) && $AsMutable(AbstractCity1) == AbstractCity1;

axiom $IsMemberlessType(AbstractCity1);

axiom (forall $U: name :: { $U <: AbstractCity1 } $U <: AbstractCity1 ==> $U == AbstractCity1);

axiom C <: C;

axiom $BaseClass(C) == System.Object;

axiom C <: $BaseClass(C) && AsDirectSubClass(C, $BaseClass(C)) == C;

axiom !$IsImmutable(C) && $AsMutable(C) == C;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: C } IsHeap($h) && $h[$oi, $inv] <: C && $h[$oi, $localinv] != System.Object ==> (forall ^i: int :: 0 <= ^i && ^i <= $Length($h[$oi, C.others]) - 1 ==> $IsNotNull(RefArrayGet($h[$h[$oi, C.others], $elements], ^i), AbstractCity1) ==> $h[RefArrayGet($h[$h[$oi, C.others], $elements], ^i), AbstractCity1.a1] != null ==> $h[$h[RefArrayGet($h[$h[$oi, C.others], $elements], ^i), AbstractCity1.a1], A.z] == 7));

procedure A..cctor();
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A..cctor()
{

  entry:
    goto block9554;

  block9554:
    goto block9605;

  block9605:
    // ----- nop
    // ----- return
    return;

}



procedure B.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation B.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, local0: bool where true, local1: int where InRange(local1, System.Int32), stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, local2: bool where true, stack1o: ref, SS$Display.Return.Local: bool where true, stack50000o: ref, $Heap$block10166$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, B);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block10132;

  block10132:
    goto block10149;

  block10149:
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(37,3)
    local0 := true;
    // ----- load constant 0
    local1 := 0;
    goto block10166$LoopPreheader;

  block10166:
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: $Heap$block10166$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block10166$LoopPreheader[$ot, $allocated] == true && $Heap$block10166$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block10166$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block10166$LoopPreheader[$ot, $ownerFrame]) && $Heap$block10166$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field
    assume (forall $o: ref :: ($Heap$block10166$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block10166$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block10166$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block10166$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields
    assert (forall $o: ref :: $o != null && $Heap$block10166$LoopPreheader[$o, $allocated] == true ==> $Heap$block10166$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block10166$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, B.others];
    // ----- array length
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true10166to10353, false10166to10183;

  true10166to10353:
    assume local1 > stack0i;
    goto block10353;

  false10166to10183:
    assume local1 <= stack0i;
    goto block10183;

  block10353:
    // ----- copy
    // ----- branch
    goto true10353to10455, false10353to10370;

  block10183:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, B.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- is instance
    stack0o := $As(stack0o, AbstractCity0);
    // ----- unary operator
    // ----- branch
    goto true10183to10285, false10183to10200;

  true10353to10455:
    assume local0;
    goto block10455;

  false10353to10370:
    assume !local0;
    goto block10370;

  block10455:
    // ----- load constant 1
    local2 := true;
    // ----- branch
    goto block10472;

  block10370:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true10370to10421, false10370to10387;

  true10183to10285:
    assume stack0o == null;
    goto block10285;

  false10183to10200:
    assume stack0o != null;
    goto block10200;

  block10285:
    // ----- load constant 1
    stack0b := true;
    goto block10302;

  block10200:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, B.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- castclass
    assert $Is(stack0o, AbstractCity0);
    stack0o := stack0o;
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, AbstractCity0.a0];
    stack1o := null;
    // ----- binary operator
    // ----- branch
    goto true10200to10285, false10200to10217;

  true10370to10421:
    assume !stack0b;
    goto block10421;

  false10370to10387:
    assume stack0b;
    goto block10387;

  block10421:
    // ----- load constant 0
    local2 := false;
    // ----- branch
    goto block10472;

  block10387:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  true10200to10285:
    assume stack0o == stack1o;
    goto block10285;

  false10200to10217:
    assume stack0o != stack1o;
    goto block10217;

  block10217:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, B.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- castclass
    assert $Is(stack0o, AbstractCity0);
    stack0o := stack0o;
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, AbstractCity0.a0];
    // ----- load field
    assert stack0o != null;
    stack0i := $Heap[stack0o, A.y];
    // ----- load constant 7
    stack1i := 7;
    // ----- binary operator
    // ----- branch
    goto true10217to10251, false10217to10234;

  block10472:
    // ----- copy
    SS$Display.Return.Local := local2;
    // ----- copy
    stack0b := local2;
    // ----- return
    $result := stack0b;
    return;

  true10217to10251:
    assume stack0i == stack1i;
    goto block10251;

  false10217to10234:
    assume stack0i != stack1i;
    goto block10234;

  block10251:
    // ----- load constant 1
    stack0b := true;
    goto block10268;

  block10234:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block10268;

  block10302:
    // ----- copy
    local0 := stack0b;
    // ----- copy
    // ----- branch
    goto true10302to10336, false10302to10319;

  true10302to10336:
    assume local0;
    goto block10336;

  false10302to10319:
    assume !local0;
    goto block10319;

  block10336:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    local1 := stack0i;
    // ----- branch
    goto block10166;

  block10319:
    // ----- branch
    goto block10353;

  block10268:
    // ----- branch
    goto block10302;

  block10166$LoopPreheader:
    $Heap$block10166$LoopPreheader := $Heap;
    goto block10166;

}



procedure B..ctor$System.Int32(this: ref, n$in: int where InRange(n$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires 0 <= n$in;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == B && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(B <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation B..ctor$System.Int32(this: ref, n$in: int)
{
  var n: int where InRange(n, System.Int32), stack0i: int, stack0o: ref, temp0: ref;

  entry:
    assume $IsNotNull(this, B);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    n := n$in;
    goto block11747;

  block11747:
    goto block11849;

  block11849:
    // ----- nop
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(42,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block11917;

  block11917:
    // ----- copy  ----- QuantifierVisibilityInvariant.ssc(44,5)
    stack0i := n;
    // ----- new array  ----- QuantifierVisibilityInvariant.ssc(44,5)
    assert 0 <= stack0i;
    havoc stack0o;
    assume $Heap[stack0o, $allocated] == false && $Length(stack0o) == stack0i;
    assume $IsNotNull(stack0o, RefArray(AbstractCity0, 1));
    assume $Heap[stack0o, $ownerRef] == stack0o && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[stack0o, $inv] == RefArray(AbstractCity0, 1) && $Heap[stack0o, $localinv] == RefArray(AbstractCity0, 1) && ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]));
    assume (forall $i: int :: RefArrayGet($Heap[stack0o, $elements], $i) == null);
    $Heap[stack0o, $allocated] := true;
    assume IsHeap($Heap);
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(44,5)
    assert this != null;
    assert !($Heap[this, $inv] <: B) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == B);
    $Heap[this, B.others] := stack0o;
    call $UpdateOwnersForRep(this, B, stack0o);
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(45,3)
    temp0 := this;
    // ----- classic pack  ----- QuantifierVisibilityInvariant.ssc(45,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert (forall ^i: int :: 0 <= ^i && ^i <= $Length($Heap[temp0, B.others]) - 1 ==> $IsNotNull(RefArrayGet($Heap[$Heap[temp0, B.others], $elements], ^i), AbstractCity0) && $Heap[RefArrayGet($Heap[$Heap[temp0, B.others], $elements], ^i), AbstractCity0.a0] != null ==> $Heap[$Heap[RefArrayGet($Heap[$Heap[temp0, B.others], $elements], ^i), AbstractCity0.a0], A.y] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == B ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := B;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure B..cctor();
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation B..cctor()
{

  entry:
    goto block12308;

  block12308:
    goto block12359;

  block12359:
    // ----- nop
    // ----- return
    return;

}



procedure C.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation C.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, local0: bool where true, local1: int where InRange(local1, System.Int32), stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, stack1o: ref, local2: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true, $Heap$block12937$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block12903;

  block12903:
    goto block12920;

  block12920:
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(51,3)
    local0 := true;
    // ----- load constant 0
    local1 := 0;
    goto block12937$LoopPreheader;

  block12937:
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: $Heap$block12937$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block12937$LoopPreheader[$ot, $allocated] == true && $Heap$block12937$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block12937$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block12937$LoopPreheader[$ot, $ownerFrame]) && $Heap$block12937$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field
    assume (forall $o: ref :: ($Heap$block12937$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block12937$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block12937$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block12937$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields
    assert (forall $o: ref :: $o != null && $Heap$block12937$LoopPreheader[$o, $allocated] == true ==> $Heap$block12937$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block12937$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, C.others];
    // ----- array length
    assert stack0o != null;
    stack0i := $Length(stack0o);
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true12937to13141, false12937to12954;

  true12937to13141:
    assume local1 > stack0i;
    goto block13141;

  false12937to12954:
    assume local1 <= stack0i;
    goto block12954;

  block13141:
    // ----- copy
    // ----- branch
    goto true13141to13243, false13141to13158;

  block12954:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, C.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- is instance
    stack0o := $As(stack0o, AbstractCity1);
    // ----- unary operator
    // ----- branch
    goto true12954to13090, false12954to12971;

  true12954to13090:
    assume stack0o == null;
    goto block13090;

  false12954to12971:
    assume stack0o != null;
    goto block12971;

  block13090:
    // ----- copy
    // ----- branch
    goto true13090to13124, false13090to13107;

  block12971:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, C.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- castclass
    assert $Is(stack0o, AbstractCity1);
    stack0o := stack0o;
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, AbstractCity1.a1];
    stack1o := null;
    // ----- binary operator
    // ----- branch
    goto true12971to13056, false12971to12988;

  true13141to13243:
    assume local0;
    goto block13243;

  false13141to13158:
    assume !local0;
    goto block13158;

  block13243:
    // ----- load constant 1
    local2 := true;
    // ----- branch
    goto block13260;

  block13158:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true13158to13209, false13158to13175;

  true13090to13124:
    assume local0;
    goto block13124;

  false13090to13107:
    assume !local0;
    goto block13107;

  block13124:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    local1 := stack0i;
    // ----- branch
    goto block12937;

  block13107:
    // ----- branch
    goto block13141;

  true12971to13056:
    assume stack0o == stack1o;
    goto block13056;

  false12971to12988:
    assume stack0o != stack1o;
    goto block12988;

  block13056:
    // ----- load constant 1
    stack0b := true;
    goto block13073;

  block12988:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, C.others];
    // ----- copy
    stack1i := local1;
    // ----- load element
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0o := RefArrayGet($Heap[stack0o, $elements], stack1i);
    // ----- castclass
    assert $Is(stack0o, AbstractCity1);
    stack0o := stack0o;
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, AbstractCity1.a1];
    // ----- load field
    assert stack0o != null;
    stack0i := $Heap[stack0o, A.z];
    // ----- load constant 7
    stack1i := 7;
    // ----- binary operator
    // ----- branch
    goto true12988to13022, false12988to13005;

  true13158to13209:
    assume !stack0b;
    goto block13209;

  false13158to13175:
    assume stack0b;
    goto block13175;

  block13209:
    // ----- load constant 0
    local2 := false;
    // ----- branch
    goto block13260;

  block13175:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  true12988to13022:
    assume stack0i == stack1i;
    goto block13022;

  false12988to13005:
    assume stack0i != stack1i;
    goto block13005;

  block13022:
    // ----- load constant 1
    stack0b := true;
    goto block13039;

  block13005:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block13039;

  block13260:
    // ----- copy
    SS$Display.Return.Local := local2;
    // ----- copy
    stack0b := local2;
    // ----- return
    $result := stack0b;
    return;

  block13073:
    // ----- copy
    local0 := stack0b;
    goto block13090;

  block13039:
    // ----- branch
    goto block13073;

  block12937$LoopPreheader:
    $Heap$block12937$LoopPreheader := $Heap;
    goto block12937;

}



procedure C..ctor$System.Int32(this: ref, n$in: int where InRange(n$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires 0 <= n$in;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == C && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(C <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation C..ctor$System.Int32(this: ref, n$in: int)
{
  var n: int where InRange(n, System.Int32), stack0i: int, stack0o: ref, temp0: ref;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    n := n$in;
    goto block14535;

  block14535:
    goto block14637;

  block14637:
    // ----- nop
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(56,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block14705;

  block14705:
    // ----- copy  ----- QuantifierVisibilityInvariant.ssc(58,5)
    stack0i := n;
    // ----- new array  ----- QuantifierVisibilityInvariant.ssc(58,5)
    assert 0 <= stack0i;
    havoc stack0o;
    assume $Heap[stack0o, $allocated] == false && $Length(stack0o) == stack0i;
    assume $IsNotNull(stack0o, RefArray(AbstractCity1, 1));
    assume $Heap[stack0o, $ownerRef] == stack0o && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[stack0o, $inv] == RefArray(AbstractCity1, 1) && $Heap[stack0o, $localinv] == RefArray(AbstractCity1, 1) && ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]));
    assume (forall $i: int :: RefArrayGet($Heap[stack0o, $elements], $i) == null);
    $Heap[stack0o, $allocated] := true;
    assume IsHeap($Heap);
    // ----- store field  ----- QuantifierVisibilityInvariant.ssc(58,5)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == C);
    $Heap[this, C.others] := stack0o;
    call $UpdateOwnersForRep(this, C, stack0o);
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(59,3)
    temp0 := this;
    // ----- classic pack  ----- QuantifierVisibilityInvariant.ssc(59,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert (forall ^i: int :: 0 <= ^i && ^i <= $Length($Heap[temp0, C.others]) - 1 ==> $IsNotNull(RefArrayGet($Heap[$Heap[temp0, C.others], $elements], ^i), AbstractCity1) ==> $Heap[RefArrayGet($Heap[$Heap[temp0, C.others], $elements], ^i), AbstractCity1.a1] != null ==> $Heap[$Heap[RefArrayGet($Heap[$Heap[temp0, C.others], $elements], ^i), AbstractCity1.a1], A.z] == 7);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := C;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure C..cctor();
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation C..cctor()
{

  entry:
    goto block15096;

  block15096:
    goto block15147;

  block15147:
    // ----- nop
    // ----- return
    return;

}



procedure AbstractCity0..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AbstractCity0 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AbstractCity0 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AbstractCity0..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, AbstractCity0);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, AbstractCity0.a0] == null;
    goto block15351;

  block15351:
    goto block15368;

  block15368:
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(62,16)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == AbstractCity0 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := AbstractCity0;
    assume IsHeap($Heap);
    return;

}



procedure AbstractCity1..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AbstractCity1 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AbstractCity1 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AbstractCity1..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, AbstractCity1);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, AbstractCity1.a1] == null;
    goto block15538;

  block15538:
    goto block15555;

  block15555:
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(66,16)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == AbstractCity1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := AbstractCity1;
    assume IsHeap($Heap);
    return;

}



axiom AnotherInvariantNameIssue <: AnotherInvariantNameIssue;

axiom $BaseClass(AnotherInvariantNameIssue) == System.Object;

axiom AnotherInvariantNameIssue <: $BaseClass(AnotherInvariantNameIssue) && AsDirectSubClass(AnotherInvariantNameIssue, $BaseClass(AnotherInvariantNameIssue)) == AnotherInvariantNameIssue;

axiom !$IsImmutable(AnotherInvariantNameIssue) && $AsMutable(AnotherInvariantNameIssue) == AnotherInvariantNameIssue;

axiom (forall $U: name :: { $U <: AnotherInvariantNameIssue } $U <: AnotherInvariantNameIssue ==> $U == AnotherInvariantNameIssue);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: AnotherInvariantNameIssue } IsHeap($h) && $h[$oi, $inv] <: AnotherInvariantNameIssue && $h[$oi, $localinv] != System.Object ==> (forall ^j: int, ^i: int :: 0 <= ^i && ^i <= $h[$oi, AnotherInvariantNameIssue.x] - 1 ==> ^i % 2 == 0 ==> ^i <= ^j && ^j <= 2 * $h[$oi, AnotherInvariantNameIssue.x] - 1 ==> ^i + ^j < 200 ==> ^i < $h[$oi, AnotherInvariantNameIssue.x]));

procedure AnotherInvariantNameIssue.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherInvariantNameIssue.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, local0: bool where true, local1: int where InRange(local1, System.Int32), stack0i: int, stack1i: int, stack0b: bool, local3: bool where true, local2: int where InRange(local2, System.Int32), SS$Display.Return.Local: bool where true, stack50000o: ref, stack0o: ref, $Heap$block16150$LoopPreheader: [ref,<x>name]x, $Heap$block16201$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, AnotherInvariantNameIssue);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block16116;

  block16116:
    goto block16133;

  block16133:
    // ----- load constant 1  ----- QuantifierVisibilityInvariant.ssc(72,3)
    local0 := true;
    // ----- load constant 0
    local1 := 0;
    goto block16150$LoopPreheader;

  block16150:
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: $Heap$block16150$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block16150$LoopPreheader[$ot, $allocated] == true && $Heap$block16150$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block16150$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block16150$LoopPreheader[$ot, $ownerFrame]) && $Heap$block16150$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field
    assume (forall $o: ref :: ($Heap$block16150$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block16150$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block16150$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block16150$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields
    assert (forall $o: ref :: $o != null && $Heap$block16150$LoopPreheader[$o, $allocated] == true ==> $Heap$block16150$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block16150$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, AnotherInvariantNameIssue.x];
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true16150to16405, false16150to16167;

  true16150to16405:
    assume local1 > stack0i;
    goto block16405;

  false16150to16167:
    assume local1 <= stack0i;
    goto block16167;

  block16405:
    // ----- copy
    // ----- branch
    goto true16405to16507, false16405to16422;

  block16167:
    // ----- load constant 2
    stack0i := 2;
    // ----- binary operator
    assert stack0i != 0;
    stack0i := local1 % stack0i;
    // ----- load constant 0
    stack1i := 0;
    // ----- binary operator
    // ----- branch
    goto true16167to16354, false16167to16184;

  true16405to16507:
    assume local0;
    goto block16507;

  false16405to16422:
    assume !local0;
    goto block16422;

  block16507:
    // ----- load constant 1
    local3 := true;
    // ----- branch
    goto block16524;

  block16422:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true16422to16473, false16422to16439;

  true16167to16354:
    assume stack0i != stack1i;
    goto block16354;

  false16167to16184:
    assume stack0i == stack1i;
    goto block16184;

  block16354:
    // ----- copy
    // ----- branch
    goto true16354to16388, false16354to16371;

  block16184:
    // ----- copy
    local2 := local1;
    goto block16201$LoopPreheader;

  true16422to16473:
    assume !stack0b;
    goto block16473;

  false16422to16439:
    assume stack0b;
    goto block16439;

  block16473:
    // ----- load constant 0
    local3 := false;
    // ----- branch
    goto block16524;

  block16439:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  true16354to16388:
    assume local0;
    goto block16388;

  false16354to16371:
    assume !local0;
    goto block16371;

  block16388:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local1 + stack0i;
    // ----- copy
    local1 := stack0i;
    // ----- branch
    goto block16150;

  block16371:
    // ----- branch
    goto block16405;

  block16524:
    // ----- copy
    SS$Display.Return.Local := local3;
    // ----- copy
    stack0b := local3;
    // ----- return
    $result := stack0b;
    return;

  block16201:
    // ----- default loop invariant: allocation and ownership are stable
    assume (forall $o: ref :: $Heap$block16201$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block16201$LoopPreheader[$ot, $allocated] == true && $Heap$block16201$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block16201$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block16201$LoopPreheader[$ot, $ownerFrame]) && $Heap$block16201$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field
    assume (forall $o: ref :: ($Heap$block16201$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block16201$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block16201$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block16201$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields
    assert (forall $o: ref :: $o != null && $Heap$block16201$LoopPreheader[$o, $allocated] == true ==> $Heap$block16201$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block16201$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 2
    stack0i := 2;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, AnotherInvariantNameIssue.x];
    // ----- binary operator
    stack0i := stack0i * stack1i;
    // ----- load constant 1
    stack1i := 1;
    // ----- binary operator
    stack0i := stack0i - stack1i;
    // ----- binary operator
    // ----- branch
    goto true16201to16354, false16201to16218;

  true16201to16354:
    assume local2 > stack0i;
    goto block16354;

  false16201to16218:
    assume local2 <= stack0i;
    goto block16218;

  block16218:
    // ----- binary operator
    stack0i := local1 + local2;
    // ----- load constant 200
    stack1i := 200;
    // ----- binary operator
    // ----- branch
    goto true16218to16303, false16218to16235;

  true16218to16303:
    assume stack0i >= stack1i;
    goto block16303;

  false16218to16235:
    assume stack0i < stack1i;
    goto block16235;

  block16303:
    // ----- copy
    // ----- branch
    goto true16303to16337, false16303to16320;

  block16235:
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, AnotherInvariantNameIssue.x];
    // ----- binary operator
    // ----- branch
    goto true16235to16269, false16235to16252;

  true16303to16337:
    assume local0;
    goto block16337;

  false16303to16320:
    assume !local0;
    goto block16320;

  block16337:
    // ----- load constant 1
    stack0i := 1;
    // ----- binary operator
    stack0i := local2 + stack0i;
    // ----- copy
    local2 := stack0i;
    // ----- branch
    goto block16201;

  block16320:
    // ----- branch
    goto block16354;

  true16235to16269:
    assume local1 < stack0i;
    goto block16269;

  false16235to16252:
    assume local1 >= stack0i;
    goto block16252;

  block16269:
    // ----- load constant 1
    stack0b := true;
    goto block16286;

  block16252:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block16286;

  block16286:
    // ----- copy
    local0 := stack0b;
    goto block16303;

  block16150$LoopPreheader:
    $Heap$block16150$LoopPreheader := $Heap;
    goto block16150;

  block16201$LoopPreheader:
    $Heap$block16201$LoopPreheader := $Heap;
    goto block16201;

}



procedure AnotherInvariantNameIssue..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AnotherInvariantNameIssue && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AnotherInvariantNameIssue <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherInvariantNameIssue..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, AnotherInvariantNameIssue);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, AnotherInvariantNameIssue.x] == 0;
    goto block17680;

  block17680:
    goto block17697;

  block17697:
    // ----- call  ----- QuantifierVisibilityInvariant.ssc(70,7)
    assert this != null;
    call System.Object..ctor(this);
    goto block17765;

  block17765:
    // ----- FrameGuard processing  ----- QuantifierVisibilityInvariant.ssc(70,31)
    temp0 := this;
    // ----- classic pack  ----- QuantifierVisibilityInvariant.ssc(70,31)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert (forall ^j: int, ^i: int :: 0 <= ^i && ^i <= $Heap[temp0, AnotherInvariantNameIssue.x] - 1 ==> ^i % 2 == 0 ==> ^i <= ^j && ^j <= 2 * $Heap[temp0, AnotherInvariantNameIssue.x] - 1 ==> ^i + ^j < 200 ==> ^i < $Heap[temp0, AnotherInvariantNameIssue.x]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherInvariantNameIssue ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := AnotherInvariantNameIssue;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure AnotherInvariantNameIssue..cctor();
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherInvariantNameIssue..cctor()
{

  entry:
    goto block18054;

  block18054:
    goto block18105;

  block18105:
    // ----- nop
    // ----- return
    return;

}


