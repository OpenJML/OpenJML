// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify LocalExpose.dll

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

const C.s: <ref>name;

const D.t: <ref>name;

const T.y: <int>name;

const S.z: <int>name;

const S.x: <int>name;

const U.u: <int>name;

const C.o: <ref>name;

const C.x: <int>name;

const C.arr: <ref>name;

const S.w: <int>name;

const System.Runtime.InteropServices._Type: name;

const System.Boolean: name;

const System.Reflection.IReflect: name;

const System.Exception: name;

const S: name;

const D: name;

const Microsoft.Contracts.GuardException: name;

const System.Runtime.Serialization.ISerializable: name;

const Microsoft.Contracts.ICheckedException: name;

const System.IComparable: name;

const System.ICloneable: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.IConvertible: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.IEquatable`1...System.String: name;

const System.IComparable`1...System.String: name;

const U: name;

const Iface: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Reflection.MemberInfo: name;

const T: name;

const System.Runtime.InteropServices._Exception: name;

const System.Collections.IEnumerable: name;

const C: name;

axiom !IsStaticField(C.x);

axiom IsDirectlyModifiableField(C.x);

axiom DeclType(C.x) == C;

axiom AsRangeField(C.x, System.Int32) == C.x;

axiom !IsStaticField(C.s);

axiom IsDirectlyModifiableField(C.s);

axiom DeclType(C.s) == C;

axiom AsNonNullRefField(C.s, System.String) == C.s;

axiom !IsStaticField(C.arr);

axiom IsDirectlyModifiableField(C.arr);

axiom DeclType(C.arr) == C;

axiom AsRefField(C.arr, ValueArray(System.Int32, 1)) == C.arr;

axiom !IsStaticField(C.o);

axiom IsDirectlyModifiableField(C.o);

axiom DeclType(C.o) == C;

axiom AsNonNullRefField(C.o, System.Object) == C.o;

axiom !IsStaticField(S.x);

axiom IsDirectlyModifiableField(S.x);

axiom DeclType(S.x) == S;

axiom AsRangeField(S.x, System.Int32) == S.x;

axiom !IsStaticField(S.z);

axiom IsDirectlyModifiableField(S.z);

axiom DeclType(S.z) == S;

axiom AsRangeField(S.z, System.Int32) == S.z;

axiom !IsStaticField(S.w);

axiom IsDirectlyModifiableField(S.w);

axiom DeclType(S.w) == S;

axiom AsRangeField(S.w, System.Int32) == S.w;

axiom !IsStaticField(T.y);

axiom IsDirectlyModifiableField(T.y);

axiom DeclType(T.y) == T;

axiom AsRangeField(T.y, System.Int32) == T.y;

axiom !IsStaticField(U.u);

axiom IsDirectlyModifiableField(U.u);

axiom DeclType(U.u) == U;

axiom AsRangeField(U.u, System.Int32) == U.u;

axiom !IsStaticField(D.t);

axiom IsDirectlyModifiableField(D.t);

axiom DeclType(D.t) == D;

axiom AsNonNullRefField(D.t, T) == D.t;

axiom Iface <: System.Object;

axiom $IsMemberlessType(Iface);

axiom C <: C;

axiom $BaseClass(C) == System.Object;

axiom C <: $BaseClass(C) && AsDirectSubClass(C, $BaseClass(C)) == C;

axiom !$IsImmutable(C) && $AsMutable(C) == C;

axiom C <: Iface;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: C } IsHeap($h) && $h[$oi, $inv] <: C && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, C.x]);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

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
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block2091;

  block2091:
    goto block2108;

  block2108:
    // ----- load constant 0  ----- LocalExpose.ssc(10,3)
    stack0i := 0;
    // ----- load field  ----- LocalExpose.ssc(10,3)
    assert this != null;
    stack1i := $Heap[this, C.x];
    // ----- binary operator  ----- LocalExpose.ssc(10,3)
    // ----- branch  ----- LocalExpose.ssc(10,3)
    goto true2108to2210, false2108to2125;

  true2108to2210:
    assume stack0i <= stack1i;
    goto block2210;

  false2108to2125:
    assume stack0i > stack1i;
    goto block2125;

  block2210:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block2227;

  block2125:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true2125to2176, false2125to2142;

  true2125to2176:
    assume !stack0b;
    goto block2176;

  false2125to2142:
    assume stack0b;
    goto block2142;

  block2176:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block2227;

  block2142:
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

  block2227:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

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



procedure C.M0(this: ref);
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



implementation C.M0(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block2975;

  block2975:
    goto block3128;

  block3128:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(14,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(14,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block3145;

  block3145:
    // ----- load field  ----- LocalExpose.ssc(15,7)
    assert this != null;
    local3 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(15,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(15,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(15,7)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block3230;

  block3230:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3230to3298, false3230to3247;

  true3230to3298:
    assume local2 == stack0o;
    goto block3298;

  false3230to3247:
    assume local2 != stack0o;
    goto block3247;

  block3298:
    // ----- classic pack  ----- LocalExpose.ssc(16,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := C;
    assume IsHeap($Heap);
    goto block3281;

  block3247:
    // ----- is instance
    // ----- branch
    goto true3247to3298, false3247to3264;

  true3247to3298:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block3298;

  false3247to3264:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block3264;

  block3264:
    // ----- branch
    goto block3281;

  block3281:
    // ----- nop
    // ----- branch
    goto block3196;

  block3196:
    // ----- return
    return;

}



axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure C.M1(this: ref);
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



implementation C.M1(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block4573;

  block4573:
    goto block4726;

  block4726:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(21,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(21,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(21,13)
    stack1o := TypeObject(C);
    // ----- local unpack  ----- LocalExpose.ssc(21,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block4743;

  block4743:
    // ----- load field  ----- LocalExpose.ssc(22,7)
    assert this != null;
    local3 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(22,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(22,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(22,7)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block4828;

  block4828:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true4828to4896, false4828to4845;

  true4828to4896:
    assume local2 == stack0o;
    goto block4896;

  false4828to4845:
    assume local2 != stack0o;
    goto block4845;

  block4896:
    // ----- load token  ----- LocalExpose.ssc(23,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(23,5)
    stack0o := TypeObject(C);
    // ----- local pack  ----- LocalExpose.ssc(23,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block4879;

  block4845:
    // ----- is instance
    // ----- branch
    goto true4845to4896, false4845to4862;

  true4845to4896:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block4896;

  false4845to4862:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block4862;

  block4862:
    // ----- branch
    goto block4879;

  block4879:
    // ----- nop
    // ----- branch
    goto block4794;

  block4794:
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

procedure C.M2(this: ref);
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



implementation C.M2(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block6001;

  block6001:
    goto block6154;

  block6154:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(28,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(28,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(28,13)
    stack1o := TypeObject(C);
    // ----- local unpack  ----- LocalExpose.ssc(28,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block6171;

  block6171:
    // ----- load field  ----- LocalExpose.ssc(29,7)
    assert this != null;
    local3 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(29,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(29,7)
    stack0i := local3 - stack0i;
    // ----- store field  ----- LocalExpose.ssc(29,7)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block6256;

  block6256:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true6256to6324, false6256to6273;

  true6256to6324:
    assume local2 == stack0o;
    goto block6324;

  false6256to6273:
    assume local2 != stack0o;
    goto block6273;

  block6324:
    // ----- load token  ----- LocalExpose.ssc(30,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(30,5)
    stack0o := TypeObject(C);
    // ----- local pack  ----- LocalExpose.ssc(30,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block6307;

  block6273:
    // ----- is instance
    // ----- branch
    goto true6273to6324, false6273to6290;

  true6273to6324:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block6324;

  false6273to6290:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block6290;

  block6290:
    // ----- branch
    goto block6307;

  block6307:
    // ----- nop
    // ----- branch
    goto block6222;

  block6222:
    // ----- return
    return;

}



procedure C.M3(this: ref);
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



implementation C.M3(this: ref)
{
  var local1: ref where $Is(local1, System.Object), stack0o: ref, stack1s: struct, stack1o: ref, local2: int where InRange(local2, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block7259;

  block7259:
    goto block7412;

  block7412:
    // ----- nop
    // ----- copy  ----- LocalExpose.ssc(35,13)
    local1 := this;
    // ----- copy  ----- LocalExpose.ssc(35,13)
    stack0o := local1;
    // ----- load token  ----- LocalExpose.ssc(35,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.Object);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(35,13)
    stack1o := TypeObject(System.Object);
    // ----- local unpack  ----- LocalExpose.ssc(35,13)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert false;
    goto block7429;

  block7429:
    // ----- load field  ----- LocalExpose.ssc(36,7)
    assert this != null;
    local2 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(36,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(36,7)
    stack0i := local2 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(36,7)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- branch
    goto block7480;

  block7480:
    // ----- copy  ----- LocalExpose.ssc(37,5)
    stack0o := local1;
    // ----- load token  ----- LocalExpose.ssc(37,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.Object);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(37,5)
    stack1o := TypeObject(System.Object);
    // ----- local pack  ----- LocalExpose.ssc(37,5)
    assert stack0o != null;
    assert false;
    // ----- nop
    // ----- branch
    goto block7446;

  block7446:
    // ----- return
    return;

}



procedure C.M5(this: ref);
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



implementation C.M5(this: ref)
{
  var local1: ref where $Is(local1, System.String), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block8126;

  block8126:
    goto block8279;

  block8279:
    // ----- nop
    // ----- load field  ----- LocalExpose.ssc(49,12)
    assert this != null;
    local1 := $Heap[this, C.s];
    // ----- copy  ----- LocalExpose.ssc(49,12)
    stack0o := local1;
    // ----- load token  ----- LocalExpose.ssc(49,12)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.String);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(49,12)
    stack1o := TypeObject(System.String);
    // ----- local unpack  ----- LocalExpose.ssc(49,12)
    assert stack0o != null;
    assert false;
    goto block8296;

  block8296:
    // ----- load constant "rustilustan"  ----- LocalExpose.ssc(50,7)
    stack0o := $stringLiteral0;
    // ----- store field  ----- LocalExpose.ssc(50,7)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, C.s] := stack0o;
    assume IsHeap($Heap);
    // ----- branch
    goto block8347;

  block8347:
    // ----- copy  ----- LocalExpose.ssc(51,5)
    stack0o := local1;
    // ----- load token  ----- LocalExpose.ssc(51,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.String);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(51,5)
    stack1o := TypeObject(System.String);
    // ----- local pack  ----- LocalExpose.ssc(51,5)
    assert stack0o != null;
    assert false;
    // ----- nop
    // ----- branch
    goto block8313;

  block8313:
    // ----- return
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

procedure C.M6(this: ref);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == C && $Heap[this, $localinv] == $typeof(this);
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



implementation C.M6(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, stack1s: struct, stack1o: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), local5: int where InRange(local5, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block9401;

  block9401:
    goto block9605;

  block9605:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(57,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(57,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block9622;

  block9622:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(58,15)
    temp2 := this;
    // ----- load token  ----- LocalExpose.ssc(58,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(58,15)
    stack1o := TypeObject(C);
    // ----- local unpack  ----- LocalExpose.ssc(58,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: C && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block9639;

  block9639:
    // ----- load field  ----- LocalExpose.ssc(59,9)
    assert this != null;
    local5 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(59,9)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(59,9)
    stack0i := local5 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(59,9)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block9775;

  block9775:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9775to9843, false9775to9792;

  true9775to9843:
    assume local4 == stack0o;
    goto block9843;

  false9775to9792:
    assume local4 != stack0o;
    goto block9792;

  block9843:
    // ----- load token  ----- LocalExpose.ssc(60,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(60,7)
    stack0o := TypeObject(C);
    // ----- local pack  ----- LocalExpose.ssc(60,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert 0 <= $Heap[temp2, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block9826;

  block9792:
    // ----- is instance
    // ----- branch
    goto true9792to9843, false9792to9809;

  true9792to9843:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block9843;

  false9792to9809:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block9809;

  block9809:
    // ----- branch
    goto block9826;

  block9826:
    // ----- nop
    // ----- branch
    goto block9690;

  block9690:
    // ----- branch
    goto block9945;

  block9945:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9945to10013, false9945to9962;

  true9945to10013:
    assume local2 == stack0o;
    goto block10013;

  false9945to9962:
    assume local2 != stack0o;
    goto block9962;

  block10013:
    // ----- classic pack  ----- LocalExpose.ssc(61,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := C;
    assume IsHeap($Heap);
    goto block9996;

  block9962:
    // ----- is instance
    // ----- branch
    goto true9962to10013, false9962to9979;

  true9962to10013:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block10013;

  false9962to9979:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block9979;

  block9979:
    // ----- branch
    goto block9996;

  block9996:
    // ----- nop
    // ----- branch
    goto block9741;

  block9741:
    // ----- return
    return;

}



procedure C.M7(this: ref);
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



implementation C.M7(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), local5: int where InRange(local5, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block11730;

  block11730:
    goto block11883;

  block11883:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(66,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(66,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(66,13)
    stack1o := TypeObject(C);
    // ----- local unpack  ----- LocalExpose.ssc(66,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: C && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block11900;

  block11900:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(67,24)
    temp2 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(67,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == C && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block11917;

  block11917:
    // ----- load field  ----- LocalExpose.ssc(68,9)
    assert this != null;
    local5 := $Heap[this, C.x];
    // ----- load constant 1  ----- LocalExpose.ssc(68,9)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(68,9)
    stack0i := local5 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(68,9)
    assert this != null;
    assert !($Heap[this, $inv] <: C) || $Heap[this, $localinv] == System.Object;
    $Heap[this, C.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block12053;

  block12053:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true12053to12121, false12053to12070;

  true12053to12121:
    assume local4 == stack0o;
    goto block12121;

  false12053to12070:
    assume local4 != stack0o;
    goto block12070;

  block12121:
    // ----- classic pack  ----- LocalExpose.ssc(69,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert 0 <= $Heap[temp2, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := C;
    assume IsHeap($Heap);
    goto block12104;

  block12070:
    // ----- is instance
    // ----- branch
    goto true12070to12121, false12070to12087;

  true12070to12121:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block12121;

  false12070to12087:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block12087;

  block12087:
    // ----- branch
    goto block12104;

  block12104:
    // ----- nop
    // ----- branch
    goto block11968;

  block11968:
    // ----- branch
    goto block12223;

  block12223:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true12223to12291, false12223to12240;

  true12223to12291:
    assume local2 == stack0o;
    goto block12291;

  false12223to12240:
    assume local2 != stack0o;
    goto block12240;

  block12291:
    // ----- load token  ----- LocalExpose.ssc(70,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(70,5)
    stack0o := TypeObject(C);
    // ----- local pack  ----- LocalExpose.ssc(70,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block12274;

  block12240:
    // ----- is instance
    // ----- branch
    goto true12240to12291, false12240to12257;

  true12240to12291:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block12291;

  false12240to12257:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block12257;

  block12257:
    // ----- branch
    goto block12274;

  block12274:
    // ----- nop
    // ----- branch
    goto block12019;

  block12019:
    // ----- return
    return;

}



procedure C..ctor(this: ref);
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



implementation C..ctor(this: ref)
{
  var stack50000o: ref, stack0o: ref, temp0: exposeVersionType, temp1: exposeVersionType, stack0i: int, temp2: exposeVersionType, temp3: ref;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, C.arr] == null;
    assume $Heap[this, C.x] == 0;
    goto block13515;

  block13515:
    goto block13532;

  block13532:
    // ----- new object  ----- LocalExpose.ssc(6,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == System.Object;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- LocalExpose.ssc(6,3)
    assert stack50000o != null;
    call System.Object..ctor(stack50000o);
    // ----- copy  ----- LocalExpose.ssc(6,3)
    stack0o := stack50000o;
    // ----- store field  ----- LocalExpose.ssc(6,3)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, C.o] := stack0o;
    assume IsHeap($Heap);
    // ----- load constant "tjolahopp"  ----- LocalExpose.ssc(7,3)
    stack0o := $stringLiteral1;
    // ----- store field  ----- LocalExpose.ssc(7,3)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, C.s] := stack0o;
    assume IsHeap($Heap);
    // ----- load constant 3  ----- LocalExpose.ssc(8,3)
    stack0i := 3;
    // ----- new array  ----- LocalExpose.ssc(8,3)
    assert 0 <= stack0i;
    havoc stack0o;
    assume $Heap[stack0o, $allocated] == false && $Length(stack0o) == stack0i;
    assume $IsNotNull(stack0o, ValueArray(System.Int32, 1));
    assume $Heap[stack0o, $ownerRef] == stack0o && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[stack0o, $inv] == ValueArray(System.Int32, 1) && $Heap[stack0o, $localinv] == ValueArray(System.Int32, 1) && ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[stack0o, $elements], $i),int) == 0);
    $Heap[stack0o, $allocated] := true;
    assume IsHeap($Heap);
    // ----- store field  ----- LocalExpose.ssc(8,3)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, C.arr] := stack0o;
    assume IsHeap($Heap);
    // ----- call  ----- LocalExpose.ssc(5,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block13600;

  block13600:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(5,14)
    temp3 := this;
    // ----- classic pack  ----- LocalExpose.ssc(5,14)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == System.Object && $Heap[temp3, $localinv] == $typeof(temp3);
    assert 0 <= $Heap[temp3, C.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := C;
    assume IsHeap($Heap);
    // ----- return
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
    goto block14042;

  block14042:
    goto block14093;

  block14093:
    // ----- nop
    // ----- return
    return;

}



axiom S <: S;

axiom $BaseClass(S) == System.Object;

axiom S <: $BaseClass(S) && AsDirectSubClass(S, $BaseClass(S)) == S;

axiom !$IsImmutable(S) && $AsMutable(S) == S;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: S } IsHeap($h) && $h[$oi, $inv] <: S && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, S.x] && 0 <= $h[$oi, S.z] && 0 <= $h[$oi, S.w]);

procedure S.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation S.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block14467;

  block14467:
    goto block14484;

  block14484:
    // ----- load constant 0  ----- LocalExpose.ssc(79,3)
    stack0i := 0;
    // ----- load field  ----- LocalExpose.ssc(79,3)
    assert this != null;
    stack1i := $Heap[this, S.x];
    // ----- binary operator  ----- LocalExpose.ssc(79,3)
    // ----- branch  ----- LocalExpose.ssc(79,3)
    goto true14484to14552, false14484to14501;

  true14484to14552:
    assume stack0i > stack1i;
    goto block14552;

  false14484to14501:
    assume stack0i <= stack1i;
    goto block14501;

  block14552:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true14552to14603, false14552to14569;

  block14501:
    // ----- load constant 0
    stack0i := 0;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, S.z];
    // ----- binary operator
    // ----- branch
    goto true14501to14552, false14501to14518;

  true14501to14552:
    assume stack0i > stack1i;
    goto block14552;

  false14501to14518:
    assume stack0i <= stack1i;
    goto block14518;

  block14518:
    // ----- load constant 0
    stack0i := 0;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, S.w];
    // ----- binary operator
    // ----- branch
    goto true14518to14552, false14518to14535;

  true14552to14603:
    assume !stack0b;
    goto block14603;

  false14552to14569:
    assume stack0b;
    goto block14569;

  block14603:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block14654;

  block14569:
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

  true14518to14552:
    assume stack0i > stack1i;
    goto block14552;

  false14518to14535:
    assume stack0i <= stack1i;
    goto block14535;

  block14535:
    // ----- branch
    goto block14637;

  block14654:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

  block14637:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block14654;

}



procedure S.V0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == S && $Heap[this, $localinv] == $typeof(this);
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



implementation S.V0(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    goto block15538;

  block15538:
    goto block15691;

  block15691:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(83,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(83,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block15708;

  block15708:
    // ----- load field  ----- LocalExpose.ssc(84,7)
    assert this != null;
    local3 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(84,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(84,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(84,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block15793;

  block15793:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true15793to15861, false15793to15810;

  true15793to15861:
    assume local2 == stack0o;
    goto block15861;

  false15793to15810:
    assume local2 != stack0o;
    goto block15810;

  block15861:
    // ----- classic pack  ----- LocalExpose.ssc(85,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := S;
    assume IsHeap($Heap);
    goto block15844;

  block15810:
    // ----- is instance
    // ----- branch
    goto true15810to15861, false15810to15827;

  true15810to15861:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block15861;

  false15810to15827:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block15827;

  block15827:
    // ----- branch
    goto block15844;

  block15844:
    // ----- nop
    // ----- branch
    goto block15759;

  block15759:
    // ----- return
    return;

}



procedure S.V1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == S && $Heap[this, $localinv] == $typeof(this);
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



implementation S.V1(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    goto block16864;

  block16864:
    goto block17017;

  block17017:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(89,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(89,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block17034;

  block17034:
    // ----- load field  ----- LocalExpose.ssc(90,7)
    assert this != null;
    local3 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(90,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(90,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(90,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block17119;

  block17119:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true17119to17187, false17119to17136;

  true17119to17187:
    assume local2 == stack0o;
    goto block17187;

  false17119to17136:
    assume local2 != stack0o;
    goto block17136;

  block17187:
    // ----- classic pack  ----- LocalExpose.ssc(91,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := S;
    assume IsHeap($Heap);
    goto block17170;

  block17136:
    // ----- is instance
    // ----- branch
    goto true17136to17187, false17136to17153;

  true17136to17187:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block17187;

  false17136to17153:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block17153;

  block17153:
    // ----- branch
    goto block17170;

  block17170:
    // ----- nop
    // ----- branch
    goto block17085;

  block17085:
    // ----- return
    return;

}



procedure S.V2(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == S && $Heap[this, $localinv] == $typeof(this);
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



implementation S.V2(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    goto block18190;

  block18190:
    goto block18343;

  block18343:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(95,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(95,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(95,13)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(95,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block18360;

  block18360:
    // ----- load field  ----- LocalExpose.ssc(96,7)
    assert this != null;
    local3 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(96,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(96,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(96,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block18445;

  block18445:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true18445to18513, false18445to18462;

  true18445to18513:
    assume local2 == stack0o;
    goto block18513;

  false18445to18462:
    assume local2 != stack0o;
    goto block18462;

  block18513:
    // ----- load token  ----- LocalExpose.ssc(97,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(97,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(97,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block18496;

  block18462:
    // ----- is instance
    // ----- branch
    goto true18462to18513, false18462to18479;

  true18462to18513:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block18513;

  false18462to18479:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block18479;

  block18479:
    // ----- branch
    goto block18496;

  block18496:
    // ----- nop
    // ----- branch
    goto block18411;

  block18411:
    // ----- return
    return;

}



procedure S.V3(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == S && $Heap[this, $localinv] == $typeof(this);
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



implementation S.V3(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    goto block19618;

  block19618:
    goto block19771;

  block19771:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(101,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(101,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(101,13)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(101,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block19788;

  block19788:
    // ----- load field  ----- LocalExpose.ssc(102,7)
    assert this != null;
    local3 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(102,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(102,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(102,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block19873;

  block19873:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true19873to19941, false19873to19890;

  true19873to19941:
    assume local2 == stack0o;
    goto block19941;

  false19873to19890:
    assume local2 != stack0o;
    goto block19890;

  block19941:
    // ----- load token  ----- LocalExpose.ssc(103,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(103,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(103,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block19924;

  block19890:
    // ----- is instance
    // ----- branch
    goto true19890to19941, false19890to19907;

  true19890to19941:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block19941;

  false19890to19907:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block19907;

  block19907:
    // ----- branch
    goto block19924;

  block19924:
    // ----- nop
    // ----- branch
    goto block19839;

  block19839:
    // ----- return
    return;

}



procedure S..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == S && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(S <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation S..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, S);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, S.x] == 0;
    assume $Heap[this, S.z] == 0;
    assume $Heap[this, S.w] == 0;
    goto block20791;

  block20791:
    goto block20808;

  block20808:
    // ----- call  ----- LocalExpose.ssc(74,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block20876;

  block20876:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(74,14)
    temp0 := this;
    // ----- classic pack  ----- LocalExpose.ssc(74,14)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := S;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure S..cctor();
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



implementation S..cctor()
{

  entry:
    goto block21165;

  block21165:
    goto block21216;

  block21216:
    // ----- nop
    // ----- return
    return;

}



axiom T <: T;

axiom $BaseClass(T) == S;

axiom T <: $BaseClass(T) && AsDirectSubClass(T, $BaseClass(T)) == T;

axiom !$IsImmutable(T) && $AsMutable(T) == T;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: T } IsHeap($h) && $h[$oi, $inv] <: T && $h[$oi, $localinv] != S ==> 0 <= $h[$oi, T.y] && $h[$oi, T.y] <= $h[$oi, S.x]);

procedure T.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation T.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block21573;

  block21573:
    goto block21590;

  block21590:
    // ----- load constant 0  ----- LocalExpose.ssc(110,3)
    stack0i := 0;
    // ----- load field  ----- LocalExpose.ssc(110,3)
    assert this != null;
    stack1i := $Heap[this, T.y];
    // ----- binary operator  ----- LocalExpose.ssc(110,3)
    // ----- branch  ----- LocalExpose.ssc(110,3)
    goto true21590to21641, false21590to21607;

  true21590to21641:
    assume stack0i > stack1i;
    goto block21641;

  false21590to21607:
    assume stack0i <= stack1i;
    goto block21607;

  block21641:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true21641to21692, false21641to21658;

  block21607:
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, T.y];
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, S.x];
    // ----- binary operator
    // ----- branch
    goto true21607to21641, false21607to21624;

  true21641to21692:
    assume !stack0b;
    goto block21692;

  false21641to21658:
    assume stack0b;
    goto block21658;

  block21692:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block21743;

  block21658:
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

  true21607to21641:
    assume stack0i > stack1i;
    goto block21641;

  false21607to21624:
    assume stack0i <= stack1i;
    goto block21624;

  block21624:
    // ----- branch
    goto block21726;

  block21743:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

  block21726:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block21743;

}



procedure T.V0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
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



implementation T.V0(this: ref)
{
  var stack0o: ref, temp0: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block22644;

  block22644:
    goto block22797;

  block22797:
    // ----- nop
    // ----- serialized AssumeStatement  ----- LocalExpose.ssc(117,5)
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    goto block22882;

  block22882:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(118,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(118,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == T && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := S;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block22899;

  block22899:
    // ----- call  ----- LocalExpose.ssc(119,7)
    assert this != null;
    call S.V0(this);
    // ----- branch
    goto block22984;

  block22984:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true22984to23052, false22984to23001;

  true22984to23052:
    assume local3 == stack0o;
    goto block23052;

  false22984to23001:
    assume local3 != stack0o;
    goto block23001;

  block23052:
    // ----- classic pack  ----- LocalExpose.ssc(120,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := T;
    assume IsHeap($Heap);
    goto block23035;

  block23001:
    // ----- is instance
    // ----- branch
    goto true23001to23052, false23001to23018;

  true23001to23052:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block23052;

  false23001to23018:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block23018;

  block23018:
    // ----- branch
    goto block23035;

  block23035:
    // ----- nop
    // ----- branch
    goto block22950;

  block22950:
    // ----- return
    return;

}



procedure T.V1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
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



implementation T.V1(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block24157;

  block24157:
    goto block24310;

  block24310:
    // ----- nop
    // ----- serialized AssumeStatement  ----- LocalExpose.ssc(124,5)
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    goto block24395;

  block24395:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(125,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(125,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(125,13)
    stack1o := TypeObject(T);
    // ----- local unpack  ----- LocalExpose.ssc(125,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: T && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := S;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block24412;

  block24412:
    // ----- call  ----- LocalExpose.ssc(126,7)
    assert this != null;
    call S.V1(this);
    // ----- branch
    goto block24497;

  block24497:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true24497to24565, false24497to24514;

  true24497to24565:
    assume local3 == stack0o;
    goto block24565;

  false24497to24514:
    assume local3 != stack0o;
    goto block24514;

  block24565:
    // ----- load token  ----- LocalExpose.ssc(127,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(127,5)
    stack0o := TypeObject(T);
    // ----- local pack  ----- LocalExpose.ssc(127,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == S;
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block24548;

  block24514:
    // ----- is instance
    // ----- branch
    goto true24514to24565, false24514to24531;

  true24514to24565:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block24565;

  false24514to24531:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block24531;

  block24531:
    // ----- branch
    goto block24548;

  block24548:
    // ----- nop
    // ----- branch
    goto block24463;

  block24463:
    // ----- return
    return;

}



procedure T.V2(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
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



implementation T.V2(this: ref)
{
  var stack0o: ref, temp0: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block25772;

  block25772:
    goto block25925;

  block25925:
    // ----- nop
    // ----- serialized AssumeStatement  ----- LocalExpose.ssc(131,5)
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    goto block26010;

  block26010:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(132,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(132,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == T && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := S;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block26027;

  block26027:
    // ----- call  ----- LocalExpose.ssc(133,7)
    assert this != null;
    call S.V2(this);
    // ----- branch
    goto block26112;

  block26112:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true26112to26180, false26112to26129;

  true26112to26180:
    assume local3 == stack0o;
    goto block26180;

  false26112to26129:
    assume local3 != stack0o;
    goto block26129;

  block26180:
    // ----- classic pack  ----- LocalExpose.ssc(134,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := T;
    assume IsHeap($Heap);
    goto block26163;

  block26129:
    // ----- is instance
    // ----- branch
    goto true26129to26180, false26129to26146;

  true26129to26180:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block26180;

  false26129to26146:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block26146;

  block26146:
    // ----- branch
    goto block26163;

  block26163:
    // ----- nop
    // ----- branch
    goto block26078;

  block26078:
    // ----- return
    return;

}



procedure T.V3(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
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



implementation T.V3(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block27285;

  block27285:
    goto block27438;

  block27438:
    // ----- nop
    // ----- serialized AssumeStatement  ----- LocalExpose.ssc(138,5)
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    goto block27523;

  block27523:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(139,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(139,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(139,13)
    stack1o := TypeObject(T);
    // ----- local unpack  ----- LocalExpose.ssc(139,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: T && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := S;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block27540;

  block27540:
    // ----- call  ----- LocalExpose.ssc(140,7)
    assert this != null;
    call S.V3(this);
    // ----- branch
    goto block27625;

  block27625:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true27625to27693, false27625to27642;

  true27625to27693:
    assume local3 == stack0o;
    goto block27693;

  false27625to27642:
    assume local3 != stack0o;
    goto block27642;

  block27693:
    // ----- load token  ----- LocalExpose.ssc(141,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(141,5)
    stack0o := TypeObject(T);
    // ----- local pack  ----- LocalExpose.ssc(141,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == S;
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block27676;

  block27642:
    // ----- is instance
    // ----- branch
    goto true27642to27693, false27642to27659;

  true27642to27693:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block27693;

  false27642to27659:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block27659;

  block27659:
    // ----- branch
    goto block27676;

  block27676:
    // ----- nop
    // ----- branch
    goto block27591;

  block27591:
    // ----- return
    return;

}



procedure T.M0(this: ref);
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



implementation T.M0(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block28815;

  block28815:
    goto block28968;

  block28968:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(145,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(145,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(145,13)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(145,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block28985;

  block28985:
    // ----- load field  ----- LocalExpose.ssc(146,7)
    assert this != null;
    local3 := $Heap[this, T.y];
    // ----- load constant 1  ----- LocalExpose.ssc(146,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(146,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(146,7)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == S;
    $Heap[this, T.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block29070;

  block29070:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true29070to29138, false29070to29087;

  true29070to29138:
    assume local2 == stack0o;
    goto block29138;

  false29070to29087:
    assume local2 != stack0o;
    goto block29087;

  block29138:
    // ----- load token  ----- LocalExpose.ssc(147,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(147,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(147,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block29121;

  block29087:
    // ----- is instance
    // ----- branch
    goto true29087to29138, false29087to29104;

  true29087to29138:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block29138;

  false29087to29104:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block29104;

  block29104:
    // ----- branch
    goto block29121;

  block29121:
    // ----- nop
    // ----- branch
    goto block29036;

  block29036:
    // ----- return
    return;

}



procedure T.M1(this: ref);
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



implementation T.M1(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block30243;

  block30243:
    goto block30396;

  block30396:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(151,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(151,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(151,13)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(151,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block30413;

  block30413:
    // ----- load field  ----- LocalExpose.ssc(152,7)
    assert this != null;
    local3 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(152,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(152,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(152,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block30498;

  block30498:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true30498to30566, false30498to30515;

  true30498to30566:
    assume local2 == stack0o;
    goto block30566;

  false30498to30515:
    assume local2 != stack0o;
    goto block30515;

  block30566:
    // ----- load token  ----- LocalExpose.ssc(153,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(153,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(153,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block30549;

  block30515:
    // ----- is instance
    // ----- branch
    goto true30515to30566, false30515to30532;

  true30515to30566:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block30566;

  false30515to30532:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block30532;

  block30532:
    // ----- branch
    goto block30549;

  block30549:
    // ----- nop
    // ----- branch
    goto block30464;

  block30464:
    // ----- return
    return;

}



procedure T.M2(this: ref);
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



implementation T.M2(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block31671;

  block31671:
    goto block31824;

  block31824:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(156,13)
    temp0 := this;
    // ----- load token  ----- LocalExpose.ssc(156,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(156,13)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(156,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block31841;

  block31841:
    // ----- load field  ----- LocalExpose.ssc(157,7)
    assert this != null;
    local3 := $Heap[this, S.z];
    // ----- load constant 1  ----- LocalExpose.ssc(157,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(157,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(157,7)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.z] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block31926;

  block31926:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true31926to31994, false31926to31943;

  true31926to31994:
    assume local2 == stack0o;
    goto block31994;

  false31926to31943:
    assume local2 != stack0o;
    goto block31943;

  block31994:
    // ----- load token  ----- LocalExpose.ssc(158,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(158,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(158,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block31977;

  block31943:
    // ----- is instance
    // ----- branch
    goto true31943to31994, false31943to31960;

  true31943to31994:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block31994;

  false31943to31960:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block31960;

  block31960:
    // ----- branch
    goto block31977;

  block31977:
    // ----- nop
    // ----- branch
    goto block31892;

  block31892:
    // ----- return
    return;

}



procedure T..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(T <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, T.y] == 0;
    goto block32844;

  block32844:
    goto block32861;

  block32861:
    // ----- call  ----- LocalExpose.ssc(108,14)
    assert this != null;
    call S..ctor(this);
    goto block32929;

  block32929:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(108,14)
    temp0 := this;
    // ----- classic pack  ----- LocalExpose.ssc(108,14)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := T;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure T..cctor();
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



implementation T..cctor()
{

  entry:
    goto block33218;

  block33218:
    goto block33269;

  block33269:
    // ----- nop
    // ----- return
    return;

}



axiom U <: U;

axiom $BaseClass(U) == T;

axiom U <: $BaseClass(U) && AsDirectSubClass(U, $BaseClass(U)) == U;

axiom !$IsImmutable(U) && $AsMutable(U) == U;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: U } IsHeap($h) && $h[$oi, $inv] <: U && $h[$oi, $localinv] != T ==> 0 <= $h[$oi, U.u]);

procedure U.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation U.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, U);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block33592;

  block33592:
    goto block33609;

  block33609:
    // ----- load constant 0  ----- LocalExpose.ssc(164,3)
    stack0i := 0;
    // ----- load field  ----- LocalExpose.ssc(164,3)
    assert this != null;
    stack1i := $Heap[this, U.u];
    // ----- binary operator  ----- LocalExpose.ssc(164,3)
    // ----- branch  ----- LocalExpose.ssc(164,3)
    goto true33609to33711, false33609to33626;

  true33609to33711:
    assume stack0i <= stack1i;
    goto block33711;

  false33609to33626:
    assume stack0i > stack1i;
    goto block33626;

  block33711:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block33728;

  block33626:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true33626to33677, false33626to33643;

  true33626to33677:
    assume !stack0b;
    goto block33677;

  false33626to33643:
    assume stack0b;
    goto block33643;

  block33677:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block33728;

  block33643:
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

  block33728:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

}



procedure U.N0(this: ref);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == U && $Heap[this, $localinv] == $typeof(this);
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



implementation U.N0(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, temp2: ref, stack1s: struct, stack1o: ref, temp3: exposeVersionType, local5: ref where $Is(local5, System.Exception), local6: int where InRange(local6, System.Int32), local7: int where InRange(local7, System.Int32), stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, U);
    assume $Heap[this, $allocated] == true;
    goto block34765;

  block34765:
    goto block34969;

  block34969:
    // ----- nop
    // ----- FrameGuard processing  ----- LocalExpose.ssc(169,22)
    temp0 := this;
    // ----- classic unpack  ----- LocalExpose.ssc(169,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == U && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := T;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block34986;

  block34986:
    // ----- load field  ----- LocalExpose.ssc(170,7)
    assert this != null;
    local3 := $Heap[this, U.u];
    // ----- load constant 1  ----- LocalExpose.ssc(170,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(170,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(170,7)
    assert this != null;
    assert !($Heap[this, $inv] <: U) || $Heap[this, $localinv] == T;
    $Heap[this, U.u] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- FrameGuard processing  ----- LocalExpose.ssc(171,15)
    temp2 := this;
    // ----- load token  ----- LocalExpose.ssc(171,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(171,15)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(171,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: S && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local5 := null;
    goto block35003;

  block35003:
    // ----- load field  ----- LocalExpose.ssc(172,9)
    assert this != null;
    local6 := $Heap[this, U.u];
    // ----- load constant 1  ----- LocalExpose.ssc(172,9)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(172,9)
    stack0i := local6 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(172,9)
    assert this != null;
    assert !($Heap[this, $inv] <: U) || $Heap[this, $localinv] == T;
    $Heap[this, U.u] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local6;
    // ----- load field  ----- LocalExpose.ssc(173,9)
    assert this != null;
    local7 := $Heap[this, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(173,9)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(173,9)
    stack0i := local7 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(173,9)
    assert this != null;
    assert !($Heap[this, $inv] <: S);
    $Heap[this, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local7;
    // ----- branch
    goto block35139;

  block35139:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true35139to35207, false35139to35156;

  true35139to35207:
    assume local5 == stack0o;
    goto block35207;

  false35139to35156:
    assume local5 != stack0o;
    goto block35156;

  block35207:
    // ----- load token  ----- LocalExpose.ssc(174,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(174,7)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(174,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert 0 <= $Heap[temp2, S.x] && 0 <= $Heap[temp2, S.z] && 0 <= $Heap[temp2, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block35190;

  block35156:
    // ----- is instance
    // ----- branch
    goto true35156to35207, false35156to35173;

  true35156to35207:
    assume $As(local5, Microsoft.Contracts.ICheckedException) != null;
    goto block35207;

  false35156to35173:
    assume $As(local5, Microsoft.Contracts.ICheckedException) == null;
    goto block35173;

  block35173:
    // ----- branch
    goto block35190;

  block35190:
    // ----- nop
    // ----- branch
    goto block35054;

  block35054:
    // ----- branch
    goto block35309;

  block35309:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true35309to35377, false35309to35326;

  true35309to35377:
    assume local2 == stack0o;
    goto block35377;

  false35309to35326:
    assume local2 != stack0o;
    goto block35326;

  block35377:
    // ----- classic pack  ----- LocalExpose.ssc(175,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == T && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, U.u];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == U ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := U;
    assume IsHeap($Heap);
    goto block35360;

  block35326:
    // ----- is instance
    // ----- branch
    goto true35326to35377, false35326to35343;

  true35326to35377:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block35377;

  false35326to35343:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block35343;

  block35343:
    // ----- branch
    goto block35360;

  block35360:
    // ----- nop
    // ----- branch
    goto block35105;

  block35105:
    // ----- return
    return;

}



procedure U..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == U && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(U <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation U..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, U);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, U.u] == 0;
    goto block36771;

  block36771:
    goto block36788;

  block36788:
    // ----- call  ----- LocalExpose.ssc(162,14)
    assert this != null;
    call T..ctor(this);
    goto block36856;

  block36856:
    // ----- FrameGuard processing  ----- LocalExpose.ssc(162,14)
    temp0 := this;
    // ----- classic pack  ----- LocalExpose.ssc(162,14)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == T && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, U.u];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == U ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := U;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure U..cctor();
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



implementation U..cctor()
{

  entry:
    goto block37145;

  block37145:
    goto block37196;

  block37196:
    // ----- nop
    // ----- return
    return;

}



axiom D <: D;

axiom $BaseClass(D) == System.Object;

axiom D <: $BaseClass(D) && AsDirectSubClass(D, $BaseClass(D)) == D;

axiom !$IsImmutable(D) && $AsMutable(D) == D;

procedure D.M0(this: ref);
  // user-declared preconditions
  requires ($Heap[$Heap[this, D.t], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, D.t], $ownerRef], $inv] <: $Heap[$Heap[this, D.t], $ownerFrame]) || $Heap[$Heap[$Heap[this, D.t], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, D.t], $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$Heap[this, D.t], $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$Heap[this, D.t], $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation D.M0(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: ref where $Is(local3, T), local4: int where InRange(local4, System.Int32), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, D);
    assume $Heap[this, $allocated] == true;
    goto block37723;

  block37723:
    goto block37876;

  block37876:
    // ----- nop
    // ----- load field  ----- LocalExpose.ssc(186,12)
    assert this != null;
    stack0o := $Heap[this, D.t];
    // ----- FrameGuard processing  ----- LocalExpose.ssc(186,12)
    temp0 := stack0o;
    // ----- load token  ----- LocalExpose.ssc(186,12)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(186,12)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(186,12)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block37893;

  block37893:
    // ----- load field  ----- LocalExpose.ssc(187,7)
    assert this != null;
    local3 := $Heap[this, D.t];
    // ----- load field  ----- LocalExpose.ssc(187,7)
    assert local3 != null;
    local4 := $Heap[local3, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(187,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(187,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(187,7)
    assert local3 != null;
    assert !($Heap[local3, $inv] <: S);
    $Heap[local3, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block37978;

  block37978:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true37978to38046, false37978to37995;

  true37978to38046:
    assume local2 == stack0o;
    goto block38046;

  false37978to37995:
    assume local2 != stack0o;
    goto block37995;

  block38046:
    // ----- load token  ----- LocalExpose.ssc(188,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(188,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(188,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block38029;

  block37995:
    // ----- is instance
    // ----- branch
    goto true37995to38046, false37995to38012;

  true37995to38046:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block38046;

  false37995to38012:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block38012;

  block38012:
    // ----- branch
    goto block38029;

  block38029:
    // ----- nop
    // ----- branch
    goto block37944;

  block37944:
    // ----- return
    return;

}



procedure D.M1(this: ref);
  // user-declared preconditions
  requires ($Heap[$Heap[this, D.t], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, D.t], $ownerRef], $inv] <: $Heap[$Heap[this, D.t], $ownerFrame]) || $Heap[$Heap[$Heap[this, D.t], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, D.t], $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$Heap[this, D.t], $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$Heap[this, D.t], $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation D.M1(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: ref where $Is(local3, T), local4: int where InRange(local4, System.Int32), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, D);
    assume $Heap[this, $allocated] == true;
    goto block39185;

  block39185:
    goto block39338;

  block39338:
    // ----- nop
    // ----- load field  ----- LocalExpose.ssc(194,12)
    assert this != null;
    stack0o := $Heap[this, D.t];
    // ----- FrameGuard processing  ----- LocalExpose.ssc(194,12)
    temp0 := stack0o;
    // ----- load token  ----- LocalExpose.ssc(194,12)
    havoc stack1s;
    assume $IsTokenForType(stack1s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(194,12)
    stack1o := TypeObject(S);
    // ----- local unpack  ----- LocalExpose.ssc(194,12)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: S && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block39355;

  block39355:
    // ----- load field  ----- LocalExpose.ssc(195,7)
    assert this != null;
    local3 := $Heap[this, D.t];
    // ----- load field  ----- LocalExpose.ssc(195,7)
    assert local3 != null;
    local4 := $Heap[local3, S.w];
    // ----- load constant 1  ----- LocalExpose.ssc(195,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(195,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(195,7)
    assert local3 != null;
    assert !($Heap[local3, $inv] <: S);
    $Heap[local3, S.w] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block39440;

  block39440:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true39440to39508, false39440to39457;

  true39440to39508:
    assume local2 == stack0o;
    goto block39508;

  false39440to39457:
    assume local2 != stack0o;
    goto block39457;

  block39508:
    // ----- load token  ----- LocalExpose.ssc(196,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, S);
    // ----- statically resolved GetTypeFromHandle call  ----- LocalExpose.ssc(196,5)
    stack0o := TypeObject(S);
    // ----- local pack  ----- LocalExpose.ssc(196,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, S.x] && 0 <= $Heap[temp0, S.z] && 0 <= $Heap[temp0, S.w];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == S ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block39491;

  block39457:
    // ----- is instance
    // ----- branch
    goto true39457to39508, false39457to39474;

  true39457to39508:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block39508;

  false39457to39474:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block39474;

  block39474:
    // ----- branch
    goto block39491;

  block39491:
    // ----- nop
    // ----- branch
    goto block39406;

  block39406:
    // ----- return
    return;

}



procedure D.M2(this: ref);
  // user-declared preconditions
  requires ($Heap[$Heap[this, D.t], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, D.t], $ownerRef], $inv] <: $Heap[$Heap[this, D.t], $ownerFrame]) || $Heap[$Heap[$Heap[this, D.t], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, D.t], $ownerFrame])) && $Heap[$Heap[this, D.t], $inv] == T && $Heap[$Heap[this, D.t], $localinv] == $typeof($Heap[this, D.t]);
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



implementation D.M2(this: ref)
{
  var stack0o: ref, temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: ref where $Is(local3, T), local4: int where InRange(local4, System.Int32), stack0i: int, stack0b: bool;

  entry:
    assume $IsNotNull(this, D);
    assume $Heap[this, $allocated] == true;
    goto block40647;

  block40647:
    goto block40800;

  block40800:
    // ----- nop
    // ----- load field  ----- LocalExpose.ssc(202,21)
    assert this != null;
    stack0o := $Heap[this, D.t];
    // ----- FrameGuard processing  ----- LocalExpose.ssc(202,21)
    temp0 := stack0o;
    // ----- classic unpack  ----- LocalExpose.ssc(202,21)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == T && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := S;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block40817;

  block40817:
    // ----- load field  ----- LocalExpose.ssc(203,7)
    assert this != null;
    local3 := $Heap[this, D.t];
    // ----- load field  ----- LocalExpose.ssc(203,7)
    assert local3 != null;
    local4 := $Heap[local3, S.x];
    // ----- load constant 1  ----- LocalExpose.ssc(203,7)
    stack0i := 1;
    // ----- binary operator  ----- LocalExpose.ssc(203,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- LocalExpose.ssc(203,7)
    assert local3 != null;
    assert !($Heap[local3, $inv] <: S);
    $Heap[local3, S.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block40902;

  block40902:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true40902to40970, false40902to40919;

  true40902to40970:
    assume local2 == stack0o;
    goto block40970;

  false40902to40919:
    assume local2 != stack0o;
    goto block40919;

  block40970:
    // ----- classic pack  ----- LocalExpose.ssc(204,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == S && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, T.y] && $Heap[temp0, T.y] <= $Heap[temp0, S.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := T;
    assume IsHeap($Heap);
    goto block40953;

  block40919:
    // ----- is instance
    // ----- branch
    goto true40919to40970, false40919to40936;

  true40919to40970:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block40970;

  false40919to40936:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block40936;

  block40936:
    // ----- branch
    goto block40953;

  block40953:
    // ----- nop
    // ----- branch
    goto block40868;

  block40868:
    // ----- return
    return;

}



procedure D..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == D && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(D <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation D..ctor(this: ref)
{
  var stack50000o: ref, stack0o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, D);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block41684;

  block41684:
    goto block41701;

  block41701:
    // ----- new object  ----- LocalExpose.ssc(181,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == T;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- LocalExpose.ssc(181,3)
    assert stack50000o != null;
    call T..ctor(stack50000o);
    // ----- copy  ----- LocalExpose.ssc(181,3)
    stack0o := stack50000o;
    // ----- store field  ----- LocalExpose.ssc(181,3)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, D.t] := stack0o;
    assume IsHeap($Heap);
    // ----- call  ----- LocalExpose.ssc(180,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == D ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := D;
    assume IsHeap($Heap);
    return;

}



const $stringLiteral0: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && $StringLength($stringLiteral0) == 11;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral0) == $stringLiteral0;

const $stringLiteral1: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral1, $allocated] } IsHeap(heap) ==> heap[$stringLiteral1, $allocated]) && $IsNotNull($stringLiteral1, System.String) && $StringLength($stringLiteral1) == 9;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral1, $allocated] } IsHeap(heap) ==> heap[$stringLiteral1, $allocated]) && $IsNotNull($stringLiteral1, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral1) == $stringLiteral1;
