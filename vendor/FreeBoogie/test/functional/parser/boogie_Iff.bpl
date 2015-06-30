// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify Iff.dll

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

const System.IComparable`1...System.String: name;

const System.IEquatable`1...System.String: name;

const System.ICloneable: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.IConvertible: name;

const System.Boolean: name;

const System.IComparable: name;

const System.Collections.IEnumerable: name;

const Iff: name;

axiom Iff <: Iff;

axiom $BaseClass(Iff) == System.Object;

axiom Iff <: $BaseClass(Iff) && AsDirectSubClass(Iff, $BaseClass(Iff)) == Iff;

axiom !$IsImmutable(Iff) && $AsMutable(Iff) == Iff;

axiom (forall $U: name :: { $U <: Iff } $U <: Iff ==> $U == Iff);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Iff.M$System.Boolean$System.Boolean(this: ref, x$in: bool where true, y$in: bool where true) returns ($result: bool where true);
  free requires true;
  free requires true;
  // user-declared preconditions
  requires x$in <==> y$in;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result;
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



implementation Iff.M$System.Boolean$System.Boolean(this: ref, x$in: bool, y$in: bool) returns ($result: bool)
{
  var x: bool where true, y: bool where true, stack0b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Iff);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    y := y$in;
    goto block1479;

  block1479:
    goto block1632;

  block1632:
    // ----- nop
    // ----- binary operator  ----- Iff.ssc(6,5)
    // ----- branch  ----- Iff.ssc(6,5)
    goto true1632to1666, false1632to1649;

  true1632to1666:
    assume x == y;
    goto block1666;

  false1632to1649:
    assume x != y;
    goto block1649;

  block1666:
    // ----- load constant 1
    stack0b := true;
    goto block1683;

  block1649:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block1683;

  block1683:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block1785;

  block1785:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



procedure Iff.P$System.Boolean$System.Boolean(this: ref, x$in: bool where true, y$in: bool where true) returns ($result: bool where true);
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result == (x$in <==> y$in);
  ensures $result == x$in <==> y$in;
  ensures $result == x$in <==> y$in;
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



implementation Iff.P$System.Boolean$System.Boolean(this: ref, x$in: bool, y$in: bool) returns ($result: bool)
{
  var x: bool where true, y: bool where true, stack0b: bool, b: bool where true, stack0o: ref, stack1b: bool, stack2b: bool, stack3b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Iff);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    y := y$in;
    goto block3723;

  block3723:
    goto block3740;

  block3740:
    // ----- binary operator  ----- Iff.ssc(16,5)
    // ----- branch  ----- Iff.ssc(16,5)
    goto true3740to3774, false3740to3757;

  true3740to3774:
    assume x == y;
    goto block3774;

  false3740to3757:
    assume x != y;
    goto block3757;

  block3774:
    // ----- load constant 1
    stack0b := true;
    goto block3791;

  block3757:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3791;

  block3791:
    // ----- copy
    b := stack0b;
    // ----- binary operator  ----- Iff.ssc(17,5)
    // ----- branch  ----- Iff.ssc(17,5)
    goto true3791to3825, false3791to3808;

  true3791to3825:
    assume b == x;
    goto block3825;

  false3791to3808:
    assume b != x;
    goto block3808;

  block3825:
    // ----- load constant 1
    stack0b := true;
    goto block3842;

  block3808:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3842;

  block3842:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(18,5)
    assert b == y;
    goto block3927;

  block3927:
    // ----- nop
    // ----- binary operator  ----- Iff.ssc(19,5)
    // ----- branch  ----- Iff.ssc(19,5)
    goto true3927to3961, false3927to3944;

  true3927to3961:
    assume b == b;
    goto block3961;

  false3927to3944:
    assume b != b;
    goto block3944;

  block3961:
    // ----- load constant 1
    stack0b := true;
    goto block3978;

  block3944:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3978;

  block3978:
    // ----- binary operator
    // ----- branch
    goto true3978to4012, false3978to3995;

  true3978to4012:
    assume b != y;
    goto block4012;

  false3978to3995:
    assume b == y;
    goto block3995;

  block4012:
    // ----- load constant 1
    stack1b := true;
    goto block4029;

  block3995:
    // ----- load constant 0
    stack1b := false;
    // ----- branch
    goto block4029;

  block4029:
    // ----- binary operator
    // ----- branch
    goto true4029to4063, false4029to4046;

  true4029to4063:
    assume stack0b == stack1b;
    goto block4063;

  false4029to4046:
    assume stack0b != stack1b;
    goto block4046;

  block4063:
    // ----- load constant 1
    stack0b := true;
    goto block4080;

  block4046:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block4080;

  block4080:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(20,5)
    assert !b;
    goto block4216;

  block4216:
    // ----- nop
    // ----- copy  ----- Iff.ssc(21,5)
    // ----- branch  ----- Iff.ssc(21,5)
    goto true4216to4301, false4216to4233;

  true4216to4301:
    assume b;
    goto block4301;

  false4216to4233:
    assume !b;
    goto block4233;

  block4301:
    // ----- binary operator
    // ----- branch
    goto true4301to4335, false4301to4318;

  block4233:
    // ----- copy
    stack0b := x;
    // ----- unary operator
    // ----- branch
    goto true4233to4267, false4233to4250;

  true4233to4267:
    assume !stack0b;
    goto block4267;

  false4233to4250:
    assume stack0b;
    goto block4250;

  block4267:
    // ----- load constant 1
    stack0b := true;
    goto block4284;

  block4250:
    // ----- copy
    stack0b := y;
    // ----- branch
    goto block4284;

  true4301to4335:
    assume y == x;
    goto block4335;

  false4301to4318:
    assume y != x;
    goto block4318;

  block4335:
    // ----- load constant 1
    stack0b := true;
    goto block4352;

  block4318:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block4352;

  block4284:
    // ----- branch
    goto block4352;

  block4352:
    // ----- copy
    b := stack0b;
    // ----- copy  ----- Iff.ssc(22,5)
    stack0b := b;
    // ----- unary operator  ----- Iff.ssc(22,5)
    // ----- branch  ----- Iff.ssc(22,5)
    goto true4352to4437, false4352to4369;

  true4352to4437:
    assume !stack0b;
    goto block4437;

  false4352to4369:
    assume stack0b;
    goto block4369;

  block4437:
    // ----- load constant 0
    stack0b := false;
    goto block4454;

  block4369:
    // ----- copy
    stack0b := y;
    // ----- unary operator
    // ----- branch
    goto true4369to4403, false4369to4386;

  true4369to4403:
    assume !stack0b;
    goto block4403;

  false4369to4386:
    assume stack0b;
    goto block4386;

  block4403:
    // ----- load constant 1
    stack0b := true;
    goto block4420;

  block4386:
    // ----- copy
    stack0b := x;
    // ----- branch
    goto block4420;

  block4454:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(23,5)
    assert (b == x) == y;
    goto block4590;

  block4420:
    // ----- branch
    goto block4454;

  block4590:
    // ----- nop
    // ----- copy
    stack0b := x;
    // ----- copy
    stack1b := y;
    // ----- copy
    stack2b := b;
    // ----- binary operator  ----- Iff.ssc(24,5)
    // ----- branch  ----- Iff.ssc(24,5)
    goto true4590to4624, false4590to4607;

  true4590to4624:
    assume y == x;
    goto block4624;

  false4590to4607:
    assume y != x;
    goto block4607;

  block4624:
    // ----- load constant 1
    stack3b := true;
    goto block4641;

  block4607:
    // ----- load constant 0
    stack3b := false;
    // ----- branch
    goto block4641;

  block4641:
    // ----- binary operator
    // ----- branch
    goto true4641to4675, false4641to4658;

  true4641to4675:
    assume stack2b == stack3b;
    goto block4675;

  false4641to4658:
    assume stack2b != stack3b;
    goto block4658;

  block4675:
    // ----- load constant 1
    stack2b := true;
    goto block4692;

  block4658:
    // ----- load constant 0
    stack2b := false;
    // ----- branch
    goto block4692;

  block4692:
    // ----- binary operator
    // ----- branch
    goto true4692to4726, false4692to4709;

  true4692to4726:
    assume stack1b == stack2b;
    goto block4726;

  false4692to4709:
    assume stack1b != stack2b;
    goto block4709;

  block4726:
    // ----- load constant 1
    stack1b := true;
    goto block4743;

  block4709:
    // ----- load constant 0
    stack1b := false;
    // ----- branch
    goto block4743;

  block4743:
    // ----- binary operator
    // ----- branch
    goto true4743to4777, false4743to4760;

  true4743to4777:
    assume stack0b == stack1b;
    goto block4777;

  false4743to4760:
    assume stack0b != stack1b;
    goto block4760;

  block4777:
    // ----- load constant 1
    stack0b := true;
    goto block4794;

  block4760:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block4794;

  block4794:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block5253;

  block5253:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Iff.ssc(25,3)
    stack0b := return.value;
    // ----- return  ----- Iff.ssc(25,3)
    $result := stack0b;
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

procedure Iff.Q$System.Boolean$System.Boolean(this: ref, x$in: bool where true, y$in: bool where true) returns ($result: bool where true);
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result <==> x$in == y$in;
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



implementation Iff.Q$System.Boolean$System.Boolean(this: ref, x$in: bool, y$in: bool) returns ($result: bool)
{
  var x: bool where true, y: bool where true, stack0b: bool, b: bool where true, stack0o: ref, stack1b: bool, stack2b: bool, stack3b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Iff);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    y := y$in;
    goto block8534;

  block8534:
    goto block8551;

  block8551:
    // ----- binary operator  ----- Iff.ssc(30,5)
    // ----- branch  ----- Iff.ssc(30,5)
    goto true8551to8585, false8551to8568;

  true8551to8585:
    assume x == y;
    goto block8585;

  false8551to8568:
    assume x != y;
    goto block8568;

  block8585:
    // ----- load constant 1
    stack0b := true;
    goto block8602;

  block8568:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block8602;

  block8602:
    // ----- copy
    b := stack0b;
    // ----- binary operator  ----- Iff.ssc(31,5)
    // ----- branch  ----- Iff.ssc(31,5)
    goto true8602to8636, false8602to8619;

  true8602to8636:
    assume b == x;
    goto block8636;

  false8602to8619:
    assume b != x;
    goto block8619;

  block8636:
    // ----- load constant 1
    stack0b := true;
    goto block8653;

  block8619:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block8653;

  block8653:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(32,5)
    assert b == y;
    goto block8738;

  block8738:
    // ----- nop
    // ----- binary operator  ----- Iff.ssc(33,5)
    // ----- branch  ----- Iff.ssc(33,5)
    goto true8738to8772, false8738to8755;

  true8738to8772:
    assume b == b;
    goto block8772;

  false8738to8755:
    assume b != b;
    goto block8755;

  block8772:
    // ----- load constant 1
    stack0b := true;
    goto block8789;

  block8755:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block8789;

  block8789:
    // ----- binary operator
    // ----- branch
    goto true8789to8823, false8789to8806;

  true8789to8823:
    assume b != y;
    goto block8823;

  false8789to8806:
    assume b == y;
    goto block8806;

  block8823:
    // ----- load constant 1
    stack1b := true;
    goto block8840;

  block8806:
    // ----- load constant 0
    stack1b := false;
    // ----- branch
    goto block8840;

  block8840:
    // ----- binary operator
    // ----- branch
    goto true8840to8874, false8840to8857;

  true8840to8874:
    assume stack0b == stack1b;
    goto block8874;

  false8840to8857:
    assume stack0b != stack1b;
    goto block8857;

  block8874:
    // ----- load constant 1
    stack0b := true;
    goto block8891;

  block8857:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block8891;

  block8891:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(34,5)
    assert !b;
    goto block9027;

  block9027:
    // ----- nop
    // ----- copy  ----- Iff.ssc(35,5)
    // ----- branch  ----- Iff.ssc(35,5)
    goto true9027to9112, false9027to9044;

  true9027to9112:
    assume b;
    goto block9112;

  false9027to9044:
    assume !b;
    goto block9044;

  block9112:
    // ----- binary operator
    // ----- branch
    goto true9112to9146, false9112to9129;

  block9044:
    // ----- copy
    stack0b := x;
    // ----- unary operator
    // ----- branch
    goto true9044to9078, false9044to9061;

  true9112to9146:
    assume y == x;
    goto block9146;

  false9112to9129:
    assume y != x;
    goto block9129;

  block9146:
    // ----- load constant 1
    stack0b := true;
    goto block9163;

  block9129:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block9163;

  true9044to9078:
    assume !stack0b;
    goto block9078;

  false9044to9061:
    assume stack0b;
    goto block9061;

  block9078:
    // ----- load constant 1
    stack0b := true;
    goto block9095;

  block9061:
    // ----- copy
    stack0b := b;
    // ----- branch
    goto block9095;

  block9163:
    // ----- copy
    b := stack0b;
    // ----- copy  ----- Iff.ssc(36,5)
    stack0b := b;
    // ----- unary operator  ----- Iff.ssc(36,5)
    // ----- branch  ----- Iff.ssc(36,5)
    goto true9163to9197, false9163to9180;

  true9163to9197:
    assume !stack0b;
    goto block9197;

  false9163to9180:
    assume stack0b;
    goto block9180;

  block9197:
    // ----- copy
    stack0b := y;
    goto block9214;

  block9180:
    // ----- load constant 1
    stack0b := true;
    // ----- branch
    goto block9214;

  block9095:
    // ----- branch
    goto block9163;

  block9214:
    // ----- copy
    b := stack0b;
    // ----- copy  ----- Iff.ssc(37,5)
    stack0b := b;
    // ----- unary operator  ----- Iff.ssc(37,5)
    // ----- branch  ----- Iff.ssc(37,5)
    goto true9214to9299, false9214to9231;

  true9214to9299:
    assume !stack0b;
    goto block9299;

  false9214to9231:
    assume stack0b;
    goto block9231;

  block9299:
    // ----- load constant 0
    stack0b := false;
    goto block9316;

  block9231:
    // ----- copy
    stack0b := y;
    // ----- unary operator
    // ----- branch
    goto true9231to9265, false9231to9248;

  true9231to9265:
    assume !stack0b;
    goto block9265;

  false9231to9248:
    assume stack0b;
    goto block9248;

  block9265:
    // ----- load constant 1
    stack0b := true;
    goto block9282;

  block9248:
    // ----- copy
    stack0b := x;
    // ----- branch
    goto block9282;

  block9316:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(38,5)
    assert (b == x) == y;
    goto block9452;

  block9452:
    // ----- nop
    // ----- copy
    stack0b := x;
    // ----- copy
    stack1b := y;
    // ----- copy
    stack2b := b;
    // ----- binary operator  ----- Iff.ssc(39,5)
    // ----- branch  ----- Iff.ssc(39,5)
    goto true9452to9486, false9452to9469;

  true9452to9486:
    assume y == x;
    goto block9486;

  false9452to9469:
    assume y != x;
    goto block9469;

  block9486:
    // ----- load constant 1
    stack3b := true;
    goto block9503;

  block9469:
    // ----- load constant 0
    stack3b := false;
    // ----- branch
    goto block9503;

  block9282:
    // ----- branch
    goto block9316;

  block9503:
    // ----- binary operator
    // ----- branch
    goto true9503to9537, false9503to9520;

  true9503to9537:
    assume stack2b == stack3b;
    goto block9537;

  false9503to9520:
    assume stack2b != stack3b;
    goto block9520;

  block9537:
    // ----- load constant 1
    stack2b := true;
    goto block9554;

  block9520:
    // ----- load constant 0
    stack2b := false;
    // ----- branch
    goto block9554;

  block9554:
    // ----- binary operator
    // ----- branch
    goto true9554to9588, false9554to9571;

  true9554to9588:
    assume stack1b == stack2b;
    goto block9588;

  false9554to9571:
    assume stack1b != stack2b;
    goto block9571;

  block9588:
    // ----- load constant 1
    stack1b := true;
    goto block9605;

  block9571:
    // ----- load constant 0
    stack1b := false;
    // ----- branch
    goto block9605;

  block9605:
    // ----- binary operator
    // ----- branch
    goto true9605to9639, false9605to9622;

  true9605to9639:
    assume stack0b == stack1b;
    goto block9639;

  false9605to9622:
    assume stack0b != stack1b;
    goto block9622;

  block9639:
    // ----- load constant 1
    stack0b := true;
    goto block9656;

  block9622:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block9656;

  block9656:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block9860;

  block9860:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Iff.ssc(40,3)
    stack0b := return.value;
    // ----- return  ----- Iff.ssc(40,3)
    $result := stack0b;
    return;

}



procedure Iff.R$System.Boolean$System.Boolean(this: ref, x$in: bool where true, y$in: bool where true) returns ($result: bool where true);
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $result <==> x$in == y$in;
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



implementation Iff.R$System.Boolean$System.Boolean(this: ref, x$in: bool, y$in: bool) returns ($result: bool)
{
  var x: bool where true, y: bool where true, stack0b: bool, b: bool where true, stack0o: ref, stack1b: bool, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Iff);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    y := y$in;
    goto block12495;

  block12495:
    goto block12512;

  block12512:
    // ----- copy  ----- Iff.ssc(45,5)
    stack0b := y;
    // ----- unary operator  ----- Iff.ssc(45,5)
    // ----- branch  ----- Iff.ssc(45,5)
    goto true12512to12546, false12512to12529;

  true12512to12546:
    assume !stack0b;
    goto block12546;

  false12512to12529:
    assume stack0b;
    goto block12529;

  block12546:
    // ----- load constant 1
    stack0b := true;
    goto block12563;

  block12529:
    // ----- copy
    stack0b := x;
    // ----- branch
    goto block12563;

  block12563:
    // ----- unary operator
    // ----- branch
    goto true12563to12648, false12563to12580;

  true12563to12648:
    assume !stack0b;
    goto block12648;

  false12563to12580:
    assume stack0b;
    goto block12580;

  block12648:
    // ----- load constant 0
    stack0b := false;
    goto block12665;

  block12580:
    // ----- copy
    stack0b := x;
    // ----- unary operator
    // ----- branch
    goto true12580to12614, false12580to12597;

  true12580to12614:
    assume !stack0b;
    goto block12614;

  false12580to12597:
    assume stack0b;
    goto block12597;

  block12614:
    // ----- load constant 1
    stack0b := true;
    goto block12631;

  block12597:
    // ----- copy
    stack0b := y;
    // ----- branch
    goto block12631;

  block12665:
    // ----- copy
    b := stack0b;
    // ----- serialized AssertStatement  ----- Iff.ssc(46,5)
    assert (b == x) == y;
    goto block12801;

  block12801:
    // ----- nop
    // ----- copy
    stack0b := x;
    // ----- binary operator  ----- Iff.ssc(47,5)
    // ----- branch  ----- Iff.ssc(47,5)
    goto true12801to12835, false12801to12818;

  true12801to12835:
    assume y == b;
    goto block12835;

  false12801to12818:
    assume y != b;
    goto block12818;

  block12835:
    // ----- load constant 1
    stack1b := true;
    goto block12852;

  block12818:
    // ----- load constant 0
    stack1b := false;
    // ----- branch
    goto block12852;

  block12631:
    // ----- branch
    goto block12665;

  block12852:
    // ----- binary operator
    // ----- branch
    goto true12852to12886, false12852to12869;

  true12852to12886:
    assume stack0b == stack1b;
    goto block12886;

  false12852to12869:
    assume stack0b != stack1b;
    goto block12869;

  block12886:
    // ----- load constant 1
    stack0b := true;
    goto block12903;

  block12869:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block12903;

  block12903:
    // ----- copy
    return.value := stack0b;
    // ----- branch
    goto block13107;

  block13107:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- Iff.ssc(48,3)
    stack0b := return.value;
    // ----- return  ----- Iff.ssc(48,3)
    $result := stack0b;
    return;

}



procedure Iff..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Iff && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Iff <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Iff..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Iff);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block13991;

  block13991:
    goto block14008;

  block14008:
    // ----- call  ----- Iff.ssc(1,7)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Iff ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Iff;
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


