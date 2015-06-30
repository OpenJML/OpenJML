// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify Unsigned.dll

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

const System.Single: name;

const System.Collections.IEnumerable: name;

const System.IConvertible: name;

const System.IEquatable`1...System.String: name;

const System.Boolean: name;

const System.IComparable: name;

const System.Double: name;

const System.IComparable`1...System.String: name;

const System.ICloneable: name;

const test: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const real#1.00: real;

axiom test <: test;

axiom $BaseClass(test) == System.Object;

axiom test <: $BaseClass(test) && AsDirectSubClass(test, $BaseClass(test)) == test;

axiom !$IsImmutable(test) && $AsMutable(test) == test;

axiom (forall $U: name :: { $U <: test } $U <: test ==> $U == test);

procedure test.M(this: ref);
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



implementation test.M(this: ref)
{
  var stack0i: int, stack0b: bool;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    goto block1343;

  block1343:
    goto block1360;

  block1360:
    // ----- load constant -1  ----- Unsigned.ssc(3,5)
    stack0i := int#4294967295;
    // ----- call  ----- Unsigned.ssc(3,5)
    assert this != null;
    call stack0b := test.P$System.UInt32(this, stack0i);
    // ----- return  ----- Unsigned.ssc(4,3)
    return;

}



axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure test.P$System.UInt32(this: ref, ui$in: int where InRange(ui$in, System.UInt32)) returns ($result: bool where true);
  free requires true;
  // user-declared preconditions
  requires 0 <= ui$in;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result <==> ui$in == 1;
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



procedure test.N(this: ref);
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



implementation test.N(this: ref)
{
  var stack0b: bool;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    goto block1547;

  block1547:
    goto block1564;

  block1564:
    // ----- load constant 1  ----- Unsigned.ssc(6,5)
    stack0b := true;
    // ----- call  ----- Unsigned.ssc(6,5)
    assert this != null;
    call stack0b := test.Q$System.Boolean(this, stack0b);
    // ----- return  ----- Unsigned.ssc(7,3)
    return;

}



procedure test.Q$System.Boolean(this: ref, b$in: bool where true) returns ($result: bool where true);
  free requires true;
  // user-declared preconditions
  requires b$in == false || b$in == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result == b$in;
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



procedure test.O(this: ref);
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



implementation test.O(this: ref)
{
  var stack0i: int, stack0b: bool;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    goto block1751;

  block1751:
    goto block1768;

  block1768:
    // ----- load constant 1  ----- Unsigned.ssc(9,5)
    stack0i := 1;
    // ----- call  ----- Unsigned.ssc(9,5)
    assert this != null;
    call stack0b := test.R$System.Int32(this, stack0i);
    // ----- return  ----- Unsigned.ssc(10,3)
    return;

}



procedure test.R$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32)) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result <==> x$in == 1;
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



implementation test.P$System.UInt32(this: ref, ui$in: int) returns ($result: bool)
{
  var ui: int where InRange(ui, System.UInt32), stack0i: int, stack0b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    ui := ui$in;
    goto block2295;

  block2295:
    goto block2397;

  block2397:
    // ----- nop
    // ----- load constant 1  ----- Unsigned.ssc(17,5)
    stack0i := 1;
    // ----- binary operator  ----- Unsigned.ssc(17,5)
    // ----- branch  ----- Unsigned.ssc(17,5)
    goto true2397to2431, false2397to2414;

  true2397to2431:
    assume ui == stack0i;
    goto block2431;

  false2397to2414:
    assume ui != stack0i;
    goto block2414;

  block2431:
    // ----- load constant 1
    stack0b := true;
    goto block2448;

  block2414:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block2448;

  block2448:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block2652;

  block2652:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



implementation test.Q$System.Boolean(this: ref, b$in: bool) returns ($result: bool)
{
  var b: bool where true, return.value: bool where true, SS$Display.Return.Local: bool where true, stack0b: bool;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block3332;

  block3332:
    goto block3468;

  block3468:
    // ----- nop
    // ----- copy  ----- Unsigned.ssc(23,5)
    return.value := b;
    // ----- branch
    goto block3570;

  block3570:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



implementation test.R$System.Int32(this: ref, x$in: int) returns ($result: bool)
{
  var x: int where InRange(x, System.Int32), stack0i: int, stack0b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block4148;

  block4148:
    goto block4165;

  block4165:
    // ----- load constant 1  ----- Unsigned.ssc(28,5)
    stack0i := 1;
    // ----- binary operator  ----- Unsigned.ssc(28,5)
    // ----- branch  ----- Unsigned.ssc(28,5)
    goto true4165to4199, false4165to4182;

  true4165to4199:
    assume x == stack0i;
    goto block4199;

  false4165to4182:
    assume x != stack0i;
    goto block4182;

  block4199:
    // ----- load constant 1
    stack0b := true;
    goto block4216;

  block4182:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block4216;

  block4216:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block4420;

  block4420:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Unsigned.ssc(29,3)
    stack0b := return.value;
    // ----- return  ----- Unsigned.ssc(29,3)
    $result := stack0b;
    return;

}



procedure test.Caller0$System.UInt32(this: ref, i$in: int where InRange(i$in, System.UInt32));
  free requires true;
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



implementation test.Caller0$System.UInt32(this: ref, i$in: int)
{
  var i: int where InRange(i, System.UInt32), stack0o: ref, stack0i: int, stack1i: int, stack2i: int, stack3i: int, stack4i: int, stack5i: int, stack6i: int, stack7i: int, stack8i: int;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    i := i$in;
    goto block4913;

  block4913:
    goto block4930;

  block4930:
    // ----- serialized AssertStatement  ----- Unsigned.ssc(34,5)
    assert i >= 0;
    goto block5015;

  block5015:
    // ----- nop
    // ----- load constant -128  ----- Unsigned.ssc(36,5)
    stack0i := -128;
    // ----- load constant 0  ----- Unsigned.ssc(36,5)
    stack1i := 0;
    // ----- load constant -32768  ----- Unsigned.ssc(36,5)
    stack2i := -32768;
    // ----- load constant 0  ----- Unsigned.ssc(36,5)
    stack3i := 0;
    // ----- load constant -2147483648  ----- Unsigned.ssc(36,5)
    stack4i := int#m2147483648;
    // ----- load constant 0  ----- Unsigned.ssc(36,5)
    stack5i := 0;
    // ----- load constant -9223372036854775808  ----- Unsigned.ssc(36,5)
    stack6i := int#m9223372036854775808;
    // ----- load constant 0  ----- Unsigned.ssc(36,5)
    stack7i := 0;
    // ----- load constant 0  ----- Unsigned.ssc(36,5)
    stack8i := 0;
    // ----- call  ----- Unsigned.ssc(36,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- load constant 127  ----- Unsigned.ssc(38,5)
    stack0i := 127;
    // ----- load constant 255  ----- Unsigned.ssc(38,5)
    stack1i := 255;
    // ----- load constant 32767  ----- Unsigned.ssc(38,5)
    stack2i := 32767;
    // ----- load constant 65535  ----- Unsigned.ssc(38,5)
    stack3i := 65535;
    // ----- load constant 2147483647  ----- Unsigned.ssc(38,5)
    stack4i := int#2147483647;
    // ----- load constant -1  ----- Unsigned.ssc(38,5)
    stack5i := int#4294967295;
    // ----- load constant 9223372036854775807  ----- Unsigned.ssc(38,5)
    stack6i := int#9223372036854775807;
    // ----- load constant -1  ----- Unsigned.ssc(38,5)
    stack7i := int#18446744073709551615;
    // ----- load constant 65535  ----- Unsigned.ssc(38,5)
    stack8i := 65535;
    // ----- call  ----- Unsigned.ssc(38,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- load constant -128  ----- Unsigned.ssc(41,5)
    stack0i := -128;
    // ----- load constant 0  ----- Unsigned.ssc(41,5)
    stack1i := 0;
    // ----- load constant -32768  ----- Unsigned.ssc(41,5)
    stack2i := -32768;
    // ----- load constant 0  ----- Unsigned.ssc(41,5)
    stack3i := 0;
    // ----- load constant -2147483648  ----- Unsigned.ssc(41,5)
    stack4i := int#m2147483648;
    // ----- load constant 0  ----- Unsigned.ssc(41,5)
    stack5i := 0;
    // ----- load constant -9223372036854775808  ----- Unsigned.ssc(41,5)
    stack6i := int#m9223372036854775808;
    // ----- load constant 0  ----- Unsigned.ssc(41,5)
    stack7i := 0;
    // ----- load constant 0  ----- Unsigned.ssc(41,5)
    stack8i := 0;
    // ----- call  ----- Unsigned.ssc(41,5)
    assert this != null;
    call test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- load constant 127  ----- Unsigned.ssc(43,5)
    stack0i := 127;
    // ----- load constant 255  ----- Unsigned.ssc(43,5)
    stack1i := 255;
    // ----- load constant 32767  ----- Unsigned.ssc(43,5)
    stack2i := 32767;
    // ----- load constant 65535  ----- Unsigned.ssc(43,5)
    stack3i := 65535;
    // ----- load constant 2147483647  ----- Unsigned.ssc(43,5)
    stack4i := int#2147483647;
    // ----- load constant -1  ----- Unsigned.ssc(43,5)
    stack5i := int#4294967295;
    // ----- load constant 9223372036854775807  ----- Unsigned.ssc(43,5)
    stack6i := int#9223372036854775807;
    // ----- load constant -1  ----- Unsigned.ssc(43,5)
    stack7i := int#18446744073709551615;
    // ----- load constant 65535  ----- Unsigned.ssc(43,5)
    stack8i := 65535;
    // ----- call  ----- Unsigned.ssc(43,5)
    assert this != null;
    call test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- return  ----- Unsigned.ssc(45,3)
    return;

}



axiom System.String <: System.String;

axiom $BaseClass(System.String) == System.Object;

axiom System.String <: $BaseClass(System.String) && AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String;

axiom $IsImmutable(System.String) && $AsImmutable(System.String) == System.String;

axiom System.IComparable <: System.Object;

axiom $IsMemberlessType(System.IComparable);

axiom System.String <: System.IComparable;

axiom System.ICloneable <: System.Object;

axiom $IsMemberlessType(System.ICloneable);

axiom System.String <: System.ICloneable;

axiom System.IConvertible <: System.Object;

axiom $IsMemberlessType(System.IConvertible);

axiom System.String <: System.IConvertible;

axiom System.IComparable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IComparable`1...System.String);

axiom System.String <: System.IComparable`1...System.String;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Object;

axiom System.Collections.IEnumerable <: System.Object;

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);

axiom System.String <: System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.String <: System.Collections.IEnumerable;

axiom System.IEquatable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IEquatable`1...System.String);

axiom System.String <: System.IEquatable`1...System.String;

axiom (forall $U: name :: { $U <: System.String } $U <: System.String ==> $U == System.String);

procedure test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this: ref, sb$in: int where InRange(sb$in, System.SByte), b$in: int where InRange(b$in, System.Byte), s$in: int where InRange(s$in, System.Int16), us$in: int where InRange(us$in, System.UInt16), i$in: int where InRange(i$in, System.Int32), ui$in: int where InRange(ui$in, System.UInt32), l$in: int where InRange(l$in, System.Int64), ul$in: int where InRange(ul$in, System.UInt64), c$in: int where InRange(c$in, System.Char));
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  // user-declared preconditions
  requires -128 <= sb$in && sb$in <= 127;
  requires 0 <= b$in && b$in <= 255;
  requires -32768 <= s$in && s$in <= 32767;
  requires 0 <= us$in && us$in <= 65535;
  requires 0 <= ui$in;
  requires 0 <= ul$in;
  requires 0 <= c$in && c$in <= 65535;
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



procedure test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this: ref, sb$in: int where InRange(sb$in, System.SByte), b$in: int where InRange(b$in, System.Byte), s$in: int where InRange(s$in, System.Int16), us$in: int where InRange(us$in, System.UInt16), i$in: int where InRange(i$in, System.Int32), ui$in: int where InRange(ui$in, System.UInt32), l$in: int where InRange(l$in, System.Int64), ul$in: int where InRange(ul$in, System.UInt64), c$in: int where InRange(c$in, System.Char));
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  // user-declared preconditions
  requires -128 <= sb$in && sb$in <= 127;
  requires 0 <= b$in && b$in <= 255;
  requires -32768 <= s$in && s$in <= 32767;
  requires 0 <= us$in && us$in <= 65535;
  requires int#m2147483648 <= i$in && i$in <= int#2147483647;
  requires 0 <= ui$in && ui$in <= int#4294967295;
  requires int#m9223372036854775808 <= l$in && l$in <= int#9223372036854775807;
  requires 0 <= ul$in && ul$in <= int#18446744073709551615;
  requires 0 <= c$in && c$in <= 65535;
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



procedure test.Caller1(this: ref);
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



implementation test.Caller1(this: ref)
{
  var sb: int where InRange(sb, System.SByte), b: int where InRange(b, System.Byte), s: int where InRange(s, System.Int16), us: int where InRange(us, System.UInt16), i: int where InRange(i, System.Int32), ui: int where InRange(ui, System.UInt32), l: int where InRange(l, System.Int64), ul: int where InRange(ul, System.UInt64), c: int where InRange(c, System.Char), stack0i: int, stack1i: int, stack2i: int, stack3i: int, stack4i: int, stack5i: int, stack6i: int, stack7i: int, stack8i: int;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    goto block5933;

  block5933:
    goto block5950;

  block5950:
    // ----- load constant -128  ----- Unsigned.ssc(50,5)
    sb := -128;
    // ----- load constant 0  ----- Unsigned.ssc(51,5)
    b := 0;
    // ----- load constant -32768  ----- Unsigned.ssc(52,5)
    s := -32768;
    // ----- load constant 0  ----- Unsigned.ssc(53,5)
    us := 0;
    // ----- load constant -2147483648  ----- Unsigned.ssc(54,5)
    i := int#m2147483648;
    // ----- load constant 0  ----- Unsigned.ssc(55,5)
    ui := 0;
    // ----- load constant -9223372036854775808  ----- Unsigned.ssc(56,5)
    l := int#m9223372036854775808;
    // ----- load constant 0  ----- Unsigned.ssc(57,5)
    ul := 0;
    // ----- load constant 0  ----- Unsigned.ssc(58,5)
    c := 0;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(59,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(59,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(60,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(60,5)
    assert this != null;
    call test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- load constant 127  ----- Unsigned.ssc(62,5)
    sb := 127;
    // ----- load constant 255  ----- Unsigned.ssc(63,5)
    b := 255;
    // ----- load constant 32767  ----- Unsigned.ssc(64,5)
    s := 32767;
    // ----- load constant 65535  ----- Unsigned.ssc(65,5)
    us := 65535;
    // ----- load constant 2147483647  ----- Unsigned.ssc(66,5)
    i := int#2147483647;
    // ----- load constant -1  ----- Unsigned.ssc(67,5)
    ui := int#4294967295;
    // ----- load constant 9223372036854775807  ----- Unsigned.ssc(68,5)
    l := int#9223372036854775807;
    // ----- load constant -1  ----- Unsigned.ssc(69,5)
    ul := int#18446744073709551615;
    // ----- load constant 65535  ----- Unsigned.ssc(70,5)
    c := 65535;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(71,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(71,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(72,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(72,5)
    assert this != null;
    call test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- return  ----- Unsigned.ssc(73,3)
    return;

}



implementation test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this: ref, sb$in: int, b$in: int, s$in: int, us$in: int, i$in: int, ui$in: int, l$in: int, ul$in: int, c$in: int)
{
  var sb: int where InRange(sb, System.SByte), b: int where InRange(b, System.Byte), s: int where InRange(s, System.Int16), us: int where InRange(us, System.UInt16), i: int where InRange(i, System.Int32), ui: int where InRange(ui, System.UInt32), l: int where InRange(l, System.Int64), ul: int where InRange(ul, System.UInt64), c: int where InRange(c, System.Int32);

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    sb := sb$in;
    b := b$in;
    s := s$in;
    us := us$in;
    i := i$in;
    ui := ui$in;
    l := l$in;
    ul := ul$in;
    c := c$in;
    goto block7565;

  block7565:
    goto block8058;

  block8058:
    // ----- nop
    // ----- return
    return;

}



implementation test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this: ref, sb$in: int, b$in: int, s$in: int, us$in: int, i$in: int, ui$in: int, l$in: int, ul$in: int, c$in: int)
{
  var sb: int where InRange(sb, System.SByte), b: int where InRange(b, System.Byte), s: int where InRange(s, System.Int16), us: int where InRange(us, System.UInt16), i: int where InRange(i, System.Int32), ui: int where InRange(ui, System.UInt32), l: int where InRange(l, System.Int64), ul: int where InRange(ul, System.UInt64), c: int where InRange(c, System.Char), stack0i: int, stack1i: int, stack2i: int, stack3i: int, stack4i: int, stack5i: int, stack6i: int, stack7i: int, stack8i: int;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    sb := sb$in;
    b := b$in;
    s := s$in;
    us := us$in;
    i := i$in;
    ui := ui$in;
    l := l$in;
    ul := ul$in;
    c := c$in;
    goto block8908;

  block8908:
    goto block9571;

  block9571:
    // ----- nop
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(99,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(99,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- return
    return;

}



procedure test.KitchenSink2$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this: ref, sb$in: int where InRange(sb$in, System.SByte), b$in: int where InRange(b$in, System.Byte), s$in: int where InRange(s$in, System.Int16), us$in: int where InRange(us$in, System.UInt16), i$in: int where InRange(i$in, System.Int32), ui$in: int where InRange(ui$in, System.UInt32), l$in: int where InRange(l$in, System.Int64), ul$in: int where InRange(ul$in, System.UInt64), c$in: int where InRange(c$in, System.Char));
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
  free requires true;
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



implementation test.KitchenSink2$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this: ref, sb$in: int, b$in: int, s$in: int, us$in: int, i$in: int, ui$in: int, l$in: int, ul$in: int, c$in: int)
{
  var sb: int where InRange(sb, System.SByte), b: int where InRange(b, System.Byte), s: int where InRange(s, System.Int16), us: int where InRange(us, System.UInt16), i: int where InRange(i, System.Int32), ui: int where InRange(ui, System.UInt32), l: int where InRange(l, System.Int64), ul: int where InRange(ul, System.UInt64), c: int where InRange(c, System.Char), stack0i: int, stack1i: int, stack2i: int, stack3i: int, stack4i: int, stack5i: int, stack6i: int, stack7i: int, stack8i: int;

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    sb := sb$in;
    b := b$in;
    s := s$in;
    us := us$in;
    i := i$in;
    ui := ui$in;
    l := l$in;
    ul := ul$in;
    c := c$in;
    goto block9945;

  block9945:
    goto block9962;

  block9962:
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(104,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(104,5)
    assert this != null;
    call test.KitchenSink0$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Int32(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack0i := sb;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack1i := b;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack2i := s;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack3i := us;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack4i := i;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack5i := ui;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack6i := l;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack7i := ul;
    // ----- copy  ----- Unsigned.ssc(105,5)
    stack8i := c;
    // ----- call  ----- Unsigned.ssc(105,5)
    assert this != null;
    call test.KitchenSink1$System.SByte$System.Byte$System.Int16$System.UInt16$System.Int32$System.UInt32$System.Int64$System.UInt64$System.Char(this, stack0i, stack1i, stack2i, stack3i, stack4i, stack5i, stack6i, stack7i, stack8i);
    // ----- return  ----- Unsigned.ssc(106,3)
    return;

}



procedure test.OrRange$System.Boolean(this: ref, b$in: bool where true) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
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



implementation test.OrRange$System.Boolean(this: ref, b$in: bool) returns ($result: int)
{
  var b: bool where true, stack0b: bool, stack0i: int, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block10574;

  block10574:
    goto block10591;

  block10591:
    // ----- copy  ----- Unsigned.ssc(111,5)
    stack0b := b;
    // ----- unary operator  ----- Unsigned.ssc(111,5)
    // ----- branch  ----- Unsigned.ssc(111,5)
    goto true10591to10676, false10591to10608;

  true10591to10676:
    assume !stack0b;
    goto block10676;

  false10591to10608:
    assume stack0b;
    goto block10608;

  block10676:
    // ----- load constant 2
    stack0i := 2;
    goto block10693;

  block10608:
    // ----- copy
    // ----- branch
    goto true10608to10642, false10608to10625;

  true10608to10642:
    assume b;
    goto block10642;

  false10608to10625:
    assume !b;
    goto block10625;

  block10642:
    // ----- load constant 1
    stack0i := 1;
    goto block10659;

  block10625:
    // ----- load constant 0
    stack0i := 0;
    // ----- branch
    goto block10659;

  block10693:
    // ----- copy
    return.value := stack0i;
    // ----- branch
    goto block10710;

  block10659:
    // ----- branch
    goto block10693;

  block10710:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Unsigned.ssc(112,3)
    stack0i := return.value;
    // ----- return  ----- Unsigned.ssc(112,3)
    $result := stack0i;
    return;

}



axiom (forall $U: name :: { $U <: System.Double } $U <: System.Double ==> $U == System.Double);

procedure test.Conversions$System.UInt32$System.Double(this: ref, ui$in: int where InRange(ui$in, System.UInt32), d$in: real where true) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
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



implementation test.Conversions$System.UInt32$System.Double(this: ref, ui$in: int, d$in: real) returns ($result: int)
{
  var ui: int where InRange(ui, System.UInt32), d: real where true, stack0i: int, x: int where InRange(x, System.Int32), y: int where InRange(y, System.UInt32), stack0r: real, f: real where true, dd: real where true, local4: real where true, dx: int where InRange(dx, System.Int32), lx: int where InRange(lx, System.Int64), s: int where InRange(s, System.Int16), stack0o: ref, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    ui := ui$in;
    d := d$in;
    goto block11203;

  block11203:
    goto block11220;

  block11220:
    // ----- copy  ----- Unsigned.ssc(118,5)
    stack0i := ui;
    // ----- unary operator  ----- Unsigned.ssc(118,5)
    stack0i := $IntToInt(stack0i, System.UInt32, System.Int32);
    // ----- copy  ----- Unsigned.ssc(118,5)
    x := stack0i;
    // ----- copy  ----- Unsigned.ssc(119,5)
    y := $IntToInt(x, System.Int32, System.UInt32);
    // ----- copy  ----- Unsigned.ssc(120,5)
    stack0r := d;
    // ----- unary operator  ----- Unsigned.ssc(120,5)
    stack0r := $RealToReal(stack0r, System.Double, System.Single);
    // ----- copy  ----- Unsigned.ssc(120,5)
    f := stack0r;
    // ----- copy  ----- Unsigned.ssc(121,5)
    stack0r := f;
    // ----- unary operator  ----- Unsigned.ssc(121,5)
    stack0r := $RealToReal(stack0r, System.Single, System.Double);
    // ----- copy  ----- Unsigned.ssc(121,5)
    dd := stack0r;
    // ----- copy  ----- Unsigned.ssc(122,5)
    stack0r := dd;
    // ----- unary operator  ----- Unsigned.ssc(122,5)
    stack0r := $RealToReal(stack0r, System.Double, System.Double);
    // ----- copy  ----- Unsigned.ssc(122,5)
    local4 := stack0r;
    // ----- load constant 1  ----- Unsigned.ssc(122,5)
    stack0r := real#1.00;
    // ----- binary operator  ----- Unsigned.ssc(122,5)
    stack0r := #radd(local4, stack0r);
    // ----- unary operator  ----- Unsigned.ssc(122,5)
    stack0r := $RealToReal(stack0r, System.Double, System.Double);
    // ----- copy  ----- Unsigned.ssc(122,5)
    dd := stack0r;
    // ----- copy
    stack0r := local4;
    // ----- copy  ----- Unsigned.ssc(123,5)
    stack0r := dd;
    // ----- unary operator  ----- Unsigned.ssc(123,5)
    stack0i := $RealToInt(stack0r, System.Double, System.Int32);
    // ----- copy  ----- Unsigned.ssc(123,5)
    dx := stack0i;
    // ----- copy  ----- Unsigned.ssc(124,5)
    stack0r := dd;
    // ----- unary operator  ----- Unsigned.ssc(124,5)
    stack0i := $RealToInt(stack0r, System.Double, System.Int64);
    // ----- copy  ----- Unsigned.ssc(124,5)
    lx := stack0i;
    // ----- copy  ----- Unsigned.ssc(125,5)
    stack0i := dx;
    // ----- unary operator  ----- Unsigned.ssc(125,5)
    stack0r := $IntToReal(stack0i, System.Int32, System.Double);
    // ----- copy  ----- Unsigned.ssc(125,5)
    dd := stack0r;
    // ----- copy  ----- Unsigned.ssc(126,5)
    stack0i := lx;
    // ----- unary operator  ----- Unsigned.ssc(126,5)
    stack0r := $IntToReal(stack0i, System.Int64, System.Double);
    // ----- copy  ----- Unsigned.ssc(126,5)
    dd := stack0r;
    // ----- copy  ----- Unsigned.ssc(127,5)
    stack0i := x;
    // ----- unary operator  ----- Unsigned.ssc(127,5)
    stack0i := $IntToInt(stack0i, System.Int32, System.Int16);
    // ----- copy  ----- Unsigned.ssc(127,5)
    s := stack0i;
    // ----- copy  ----- Unsigned.ssc(128,5)
    x := $IntToInt(s, System.Int16, System.Int32);
    // ----- serialized AssertStatement  ----- Unsigned.ssc(129,5)
    assert x == s;
    goto block11305;

  block11305:
    // ----- nop
    // ----- copy  ----- Unsigned.ssc(130,5)
    stack0i := y;
    // ----- unary operator  ----- Unsigned.ssc(130,5)
    stack0i := $IntToInt(stack0i, System.UInt32, System.Int16);
    // ----- copy  ----- Unsigned.ssc(130,5)
    s := stack0i;
    // ----- copy  ----- Unsigned.ssc(131,5)
    stack0i := y;
    // ----- unary operator  ----- Unsigned.ssc(131,5)
    stack0i := $IntToInt(stack0i, System.UInt32, System.Int32);
    // ----- copy  ----- Unsigned.ssc(131,5)
    return.value := stack0i;
    // ----- branch
    goto block11322;

  block11322:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Unsigned.ssc(132,3)
    stack0i := return.value;
    // ----- return  ----- Unsigned.ssc(132,3)
    $result := stack0i;
    return;

}



axiom (forall $U: name :: { $U <: System.Single } $U <: System.Single ==> $U == System.Single);

procedure test..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(test <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, test);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block12291;

  block12291:
    goto block12308;

  block12308:
    // ----- call  ----- Unsigned.ssc(1,7)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == test ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := test;
    assume IsHeap($Heap);
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


