// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo ManualRange1

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

const Tools.Range_Enumerator.B: <int>name;

const Tools.Range_Enumerable.B: <int>name;

const Tools.Range_Enumerator.Index: <int>name;

const Tools.Range_Enumerable.A: <int>name;

const Tools.Range_Enumerator.A: <int>name;

const Test: name;

const System.Runtime.InteropServices._Type: name;

const System.IComparable: name;

const Microsoft.Contracts.ICheckedException: name;

const System.Reflection.MemberInfo: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.IComparable`1...System.String: name;

const System.Boolean: name;

const System.Runtime.InteropServices._Exception: name;

const System.IConvertible: name;

const System.Collections.IEnumerable: name;

const System.IEquatable`1...System.String: name;

const Tools.Range_Enumerator: name;

const System.ICloneable: name;

const Tools: name;

const Tools.Range_Enumerable: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Exception: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Reflection.IReflect: name;

axiom !IsStaticField(Tools.Range_Enumerator.A);

axiom IsDirectlyModifiableField(Tools.Range_Enumerator.A);

axiom DeclType(Tools.Range_Enumerator.A) == Tools.Range_Enumerator;

axiom AsRangeField(Tools.Range_Enumerator.A, System.Int32) == Tools.Range_Enumerator.A;

axiom !IsStaticField(Tools.Range_Enumerator.B);

axiom IsDirectlyModifiableField(Tools.Range_Enumerator.B);

axiom DeclType(Tools.Range_Enumerator.B) == Tools.Range_Enumerator;

axiom AsRangeField(Tools.Range_Enumerator.B, System.Int32) == Tools.Range_Enumerator.B;

axiom !IsStaticField(Tools.Range_Enumerator.Index);

axiom IsDirectlyModifiableField(Tools.Range_Enumerator.Index);

axiom DeclType(Tools.Range_Enumerator.Index) == Tools.Range_Enumerator;

axiom AsRangeField(Tools.Range_Enumerator.Index, System.Int32) == Tools.Range_Enumerator.Index;

function #Tools.Range_Enumerator.get_Current([ref,<x>name]x, ref) returns (int);

function ##Tools.Range_Enumerator.get_Current(exposeVersionType) returns (int);

axiom !IsStaticField(Tools.Range_Enumerable.A);

axiom IsDirectlyModifiableField(Tools.Range_Enumerable.A);

axiom DeclType(Tools.Range_Enumerable.A) == Tools.Range_Enumerable;

axiom AsRangeField(Tools.Range_Enumerable.A, System.Int32) == Tools.Range_Enumerable.A;

axiom !IsStaticField(Tools.Range_Enumerable.B);

axiom IsDirectlyModifiableField(Tools.Range_Enumerable.B);

axiom DeclType(Tools.Range_Enumerable.B) == Tools.Range_Enumerable;

axiom AsRangeField(Tools.Range_Enumerable.B, System.Int32) == Tools.Range_Enumerable.B;

axiom Tools <: Tools;

axiom $BaseClass(Tools) == System.Object;

axiom Tools <: $BaseClass(Tools) && AsDirectSubClass(Tools, $BaseClass(Tools)) == Tools;

axiom !$IsImmutable(Tools) && $AsMutable(Tools) == Tools;

axiom $IsMemberlessType(Tools);

axiom (forall $U: name :: { $U <: Tools } $U <: Tools ==> $U == Tools);

axiom Tools.Range_Enumerator <: Tools.Range_Enumerator;

axiom $BaseClass(Tools.Range_Enumerator) == System.Object;

axiom Tools.Range_Enumerator <: $BaseClass(Tools.Range_Enumerator) && AsDirectSubClass(Tools.Range_Enumerator, $BaseClass(Tools.Range_Enumerator)) == Tools.Range_Enumerator;

axiom !$IsImmutable(Tools.Range_Enumerator) && $AsMutable(Tools.Range_Enumerator) == Tools.Range_Enumerator;

axiom (forall $U: name :: { $U <: Tools.Range_Enumerator } $U <: Tools.Range_Enumerator ==> $U == Tools.Range_Enumerator);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Tools.Range_Enumerator } IsHeap($h) && $h[$oi, $inv] <: Tools.Range_Enumerator && $h[$oi, $localinv] != System.Object ==> true);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Tools.Range_Enumerator.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Tools.Range_Enumerator.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, return.value: bool where true, SS$Display.Return.Local: bool where true, stack0b: bool;

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerator);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block4709;

  block4709:
    goto block4726;

  block4726:
    // ----- branch
    goto block4845;

  block4845:
    goto block4862;

  block4862:
    goto block4879;

  block4879:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block4896;

  block4896:
    goto block4913;

  block4913:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



procedure Tools.Range_Enumerator..ctor$System.Int32$System.Int32(this: ref, a$in: int where InRange(a$in, System.Int32), b$in: int where InRange(b$in, System.Int32));
  free requires true;
  free requires true;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, Tools.Range_Enumerator.A] == a$in;
  ensures $Heap[this, Tools.Range_Enumerator.B] == b$in;
  ensures $Heap[this, Tools.Range_Enumerator.Index] == -1;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Tools.Range_Enumerator && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Tools.Range_Enumerator <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Tools.Range_Enumerator..ctor$System.Int32$System.Int32(this: ref, a$in: int, b$in: int)
{
  var a: int where InRange(a, System.Int32), b: int where InRange(b, System.Int32), temp0: exposeVersionType, temp1: exposeVersionType, stack0i: int, temp2: exposeVersionType, temp3: ref;

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerator);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    a := a$in;
    b := b$in;
    assume $Heap[this, Tools.Range_Enumerator.A] == 0;
    assume $Heap[this, Tools.Range_Enumerator.B] == 0;
    assume $Heap[this, Tools.Range_Enumerator.Index] == 0;
    goto block5729;

  block5729:
    goto block5746;

  block5746:
    goto block5763;

  block5763:
    goto block5780;

  block5780:
    goto block5797;

  block5797:
    // ----- store field  ----- ManualRange1.ssc(15,10)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, Tools.Range_Enumerator.A] := a;
    assume IsHeap($Heap);
    // ----- store field  ----- ManualRange1.ssc(16,10)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Tools.Range_Enumerator.B] := b;
    assume IsHeap($Heap);
    // ----- load constant -1  ----- ManualRange1.ssc(17,23)
    stack0i := -1;
    // ----- store field  ----- ManualRange1.ssc(17,10)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Tools.Range_Enumerator.Index] := stack0i;
    assume IsHeap($Heap);
    goto block5814;

  block5814:
    // ----- call  ----- ManualRange1.ssc(18,10)
    assert this != null;
    call System.Object..ctor(this);
    goto block5933;

  block5933:
    goto block5950;

  block5950:
    // ----- nop
    goto block5967;

  block5967:
    goto block5984;

  block5984:
    // ----- FrameGuard processing  ----- ManualRange1.ssc(19,7)
    temp3 := this;
    // ----- classic pack  ----- ManualRange1.ssc(19,7)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == System.Object && $Heap[temp3, $localinv] == $typeof(temp3);
    assert true;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == Tools.Range_Enumerator ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := Tools.Range_Enumerator;
    assume IsHeap($Heap);
    goto block6392;

  block6392:
    // ----- nop
    goto block6409;

  block6409:
    // ----- return  ----- ManualRange1.ssc(19,7)
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



procedure Tools.Range_Enumerator.MoveNext(this: ref) returns ($result: bool where true);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
  // user-declared postconditions
  ensures $Heap[this, Tools.Range_Enumerator.A] == old($Heap[this, Tools.Range_Enumerator.A]);
  ensures $Heap[this, Tools.Range_Enumerator.B] == old($Heap[this, Tools.Range_Enumerator.B]);
  ensures $Heap[this, Tools.Range_Enumerator.Index] == old($Heap[this, Tools.Range_Enumerator.Index]) + 1;
  ensures $result == ($Heap[this, Tools.Range_Enumerator.A] + $Heap[this, Tools.Range_Enumerator.Index] < $Heap[this, Tools.Range_Enumerator.B]);
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



implementation Tools.Range_Enumerator.MoveNext(this: ref) returns ($result: bool)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local9741: ref where $Is(local9741, System.Exception), local9758: int where InRange(local9758, System.Int32), stack0i: int, temp2: exposeVersionType, stack1i: int, stack0b: bool, return.value: bool where true, stack0o: ref, stack0s: struct, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerator);
    assume $Heap[this, $allocated] == true;
    goto block7956;

  block7956:
    goto block8228;

  block8228:
    // ----- nop
    goto block8245;

  block8245:
    // ----- FrameGuard processing  ----- ManualRange1.ssc(27,18)
    temp0 := this;
    // ----- load token  ----- ManualRange1.ssc(27,18)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Tools.Range_Enumerator);
    // ----- statically resolved GetTypeFromHandle call  ----- ManualRange1.ssc(27,18)
    stack1o := TypeObject(Tools.Range_Enumerator);
    // ----- local unpack  ----- ManualRange1.ssc(27,18)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Tools.Range_Enumerator && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local9741 := null;
    goto block8262;

  block8262:
    // ----- load field  ----- ManualRange1.ssc(29,12)
    assert this != null;
    local9758 := $Heap[this, Tools.Range_Enumerator.Index];
    // ----- load constant 1  ----- ManualRange1.ssc(29,12)
    stack0i := 1;
    // ----- binary operator  ----- ManualRange1.ssc(29,12)
    stack0i := local9758 + stack0i;
    // ----- store field  ----- ManualRange1.ssc(29,12)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Tools.Range_Enumerator.Index] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- ManualRange1.ssc(29,12)
    stack0i := local9758;
    goto block8279;

  block8279:
    // ----- nop  ----- ManualRange1.ssc(29,12)
    goto block8296;

  block8296:
    // ----- load field  ----- ManualRange1.ssc(30,19)
    assert this != null;
    stack0i := $Heap[this, Tools.Range_Enumerator.A];
    // ----- load field  ----- ManualRange1.ssc(30,28)
    assert this != null;
    stack1i := $Heap[this, Tools.Range_Enumerator.Index];
    // ----- binary operator  ----- ManualRange1.ssc(30,19)
    stack0i := stack0i + stack1i;
    // ----- load field  ----- ManualRange1.ssc(30,41)
    assert this != null;
    stack1i := $Heap[this, Tools.Range_Enumerator.B];
    // ----- binary operator  ----- ManualRange1.ssc(30,19)
    // ----- branch  ----- ManualRange1.ssc(30,19)
    goto true8296to8330, false8296to8313;

  true8296to8330:
    assume stack0i < stack1i;
    goto block8330;

  false8296to8313:
    assume stack0i >= stack1i;
    goto block8313;

  block8330:
    goto block8347;

  block8313:
    // ----- load constant False  ----- ManualRange1.ssc(30,19)
    stack0b := false;
    // ----- branch  ----- ManualRange1.ssc(30,19)
    goto block8364;

  block8364:
    goto block8381;

  block8347:
    // ----- load constant True  ----- ManualRange1.ssc(30,19)
    stack0b := true;
    goto block8364;

  block8381:
    // ----- copy  ----- ManualRange1.ssc(30,12)
    return.value := stack0b;
    // ----- branch
    goto block9163;

  block9163:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9163to9265, false9163to9180;

  true9163to9265:
    assume local9741 == stack0o;
    goto block9265;

  false9163to9180:
    assume local9741 != stack0o;
    goto block9180;

  block9265:
    goto block9282;

  block9180:
    // ----- is instance
    // ----- branch
    goto true9180to9265, false9180to9197;

  true9180to9265:
    assume $As(local9741, Microsoft.Contracts.ICheckedException) != null;
    goto block9265;

  false9180to9197:
    assume $As(local9741, Microsoft.Contracts.ICheckedException) == null;
    goto block9197;

  block9197:
    // ----- branch
    goto block9214;

  block9282:
    // ----- load token  ----- ManualRange1.ssc(31,10)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Tools.Range_Enumerator);
    // ----- statically resolved GetTypeFromHandle call  ----- ManualRange1.ssc(31,10)
    stack0o := TypeObject(Tools.Range_Enumerator);
    // ----- local pack  ----- ManualRange1.ssc(31,10)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert true;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Tools.Range_Enumerator ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block9214;

  block9214:
    goto block9231;

  block9231:
    goto block9248;

  block9248:
    // ----- nop
    // ----- branch
    goto block8534;

  block8534:
    goto block9129;

  block9129:
    // ----- nop
    goto block9146;

  block9146:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
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

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

axiom (forall $Heap: [ref,<x>name]x, this: ref :: { #Tools.Range_Enumerator.get_Current($Heap, this) } IsHeap($Heap) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> InRange(#Tools.Range_Enumerator.get_Current($Heap, this), System.Int32) && #Tools.Range_Enumerator.get_Current($Heap, this) == $Heap[this, Tools.Range_Enumerator.A] + $Heap[this, Tools.Range_Enumerator.Index]);

axiom (forall $Heap: [ref,<x>name]x, this: ref :: { #Tools.Range_Enumerator.get_Current($Heap, this) } this != null && $typeof(this) <: Tools.Range_Enumerator && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] == true ==> #Tools.Range_Enumerator.get_Current($Heap, this) == ##Tools.Range_Enumerator.get_Current($Heap[this, $exposeVersion]));

procedure Tools.Range_Enumerator.get_Current(this: ref) returns ($result: int where InRange($result, System.Int32));
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures $result == $Heap[this, Tools.Range_Enumerator.A] + $Heap[this, Tools.Range_Enumerator.Index];
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  free ensures $Heap == old($Heap);
  free ensures $result == #Tools.Range_Enumerator.get_Current($Heap, this);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Tools.Range_Enumerator.get_Current(this: ref) returns ($result: int)
{
  var stack0i: int, stack1i: int, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerator);
    assume $Heap[this, $allocated] == true;
    goto block10455;

  block10455:
    goto block10659;

  block10659:
    // ----- nop
    goto block10676;

  block10676:
    // ----- load field  ----- ManualRange1.ssc(39,20)
    assert this != null;
    stack0i := $Heap[this, Tools.Range_Enumerator.A];
    // ----- load field  ----- ManualRange1.ssc(39,29)
    assert this != null;
    stack1i := $Heap[this, Tools.Range_Enumerator.Index];
    // ----- binary operator  ----- ManualRange1.ssc(39,20)
    stack0i := stack0i + stack1i;
    // ----- copy  ----- ManualRange1.ssc(39,13)
    return.value := stack0i;
    // ----- branch
    goto block10693;

  block10693:
    goto block10897;

  block10897:
    // ----- nop
    goto block10914;

  block10914:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

}



procedure Tools.Range_Enumerator..cctor();
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



implementation Tools.Range_Enumerator..cctor()
{

  entry:
    goto block11560;

  block11560:
    goto block11679;

  block11679:
    // ----- nop
    goto block11696;

  block11696:
    goto block11713;

  block11713:
    // ----- return
    return;

}



axiom Tools.Range_Enumerable <: Tools.Range_Enumerable;

axiom $BaseClass(Tools.Range_Enumerable) == System.Object;

axiom Tools.Range_Enumerable <: $BaseClass(Tools.Range_Enumerable) && AsDirectSubClass(Tools.Range_Enumerable, $BaseClass(Tools.Range_Enumerable)) == Tools.Range_Enumerable;

axiom !$IsImmutable(Tools.Range_Enumerable) && $AsMutable(Tools.Range_Enumerable) == Tools.Range_Enumerable;

axiom (forall $U: name :: { $U <: Tools.Range_Enumerable } $U <: Tools.Range_Enumerable ==> $U == Tools.Range_Enumerable);

procedure Tools.Range_Enumerable..ctor$System.Int32$System.Int32(this: ref, a$in: int where InRange(a$in, System.Int32), b$in: int where InRange(b$in, System.Int32));
  free requires true;
  free requires true;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, Tools.Range_Enumerable.A] == a$in;
  ensures $Heap[this, Tools.Range_Enumerable.B] == b$in;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Tools.Range_Enumerable && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Tools.Range_Enumerable <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Tools.Range_Enumerable..ctor$System.Int32$System.Int32(this: ref, a$in: int, b$in: int)
{
  var a: int where InRange(a, System.Int32), b: int where InRange(b, System.Int32), temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerable);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    a := a$in;
    b := b$in;
    assume $Heap[this, Tools.Range_Enumerable.A] == 0;
    assume $Heap[this, Tools.Range_Enumerable.B] == 0;
    goto block12750;

  block12750:
    goto block12767;

  block12767:
    goto block12784;

  block12784:
    goto block12801;

  block12801:
    goto block12818;

  block12818:
    // ----- store field  ----- ManualRange1.ssc(53,10)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, Tools.Range_Enumerable.A] := a;
    assume IsHeap($Heap);
    // ----- store field  ----- ManualRange1.ssc(54,10)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Tools.Range_Enumerable.B] := b;
    assume IsHeap($Heap);
    // ----- call  ----- ManualRange1.ssc(55,10)
    assert this != null;
    call System.Object..ctor(this);
    goto block12835;

  block12835:
    goto block13141;

  block13141:
    // ----- nop
    goto block13158;

  block13158:
    // ----- return  ----- ManualRange1.ssc(56,7)
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Tools.Range_Enumerable ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Tools.Range_Enumerable;
    assume IsHeap($Heap);
    return;

}



procedure Tools.Range_Enumerable.GetEnumerator(this: ref) returns ($result: ref where $IsNotNull($result, Tools.Range_Enumerator));
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, Tools.Range_Enumerator);
  // user-declared postconditions
  ensures $Heap[this, Tools.Range_Enumerable.A] == old($Heap[this, Tools.Range_Enumerable.A]);
  ensures $Heap[this, Tools.Range_Enumerable.B] == old($Heap[this, Tools.Range_Enumerable.B]);
  ensures $Heap[$result, Tools.Range_Enumerator.A] == $Heap[this, Tools.Range_Enumerable.A];
  ensures $Heap[$result, Tools.Range_Enumerator.B] == $Heap[this, Tools.Range_Enumerable.B];
  ensures $Heap[$result, Tools.Range_Enumerator.Index] == -1;
  ensures $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder && (forall $fpc: ref :: $fpc != null && old($Heap)[$fpc, $allocated] == true ==> !($Heap[$fpc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$fpc, $ownerFrame] == $Heap[$result, $ownerFrame]));
  // return value is peer consistent
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Tools.Range_Enumerable.GetEnumerator(this: ref) returns ($result: ref)
{
  var stack0i: int, stack1i: int, stack50000o: ref, stack0o: ref, result: ref where $Is(result, Tools.Range_Enumerator), return.value: ref where $IsNotNull(return.value, Tools.Range_Enumerator), SS$Display.Return.Local: ref where $IsNotNull(SS$Display.Return.Local, Tools.Range_Enumerator);

  entry:
    assume $IsNotNull(this, Tools.Range_Enumerable);
    assume $Heap[this, $allocated] == true;
    goto block14467;

  block14467:
    goto block14586;

  block14586:
    // ----- nop
    goto block14603;

  block14603:
    // ----- load field  ----- ManualRange1.ssc(66,57)
    assert this != null;
    stack0i := $Heap[this, Tools.Range_Enumerable.A];
    // ----- load field  ----- ManualRange1.ssc(66,65)
    assert this != null;
    stack1i := $Heap[this, Tools.Range_Enumerable.B];
    // ----- new object  ----- ManualRange1.ssc(66,36)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Tools.Range_Enumerator;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- ManualRange1.ssc(66,36)
    assert stack50000o != null;
    call Tools.Range_Enumerator..ctor$System.Int32$System.Int32(stack50000o, stack0i, stack1i);
    // ----- copy  ----- ManualRange1.ssc(66,10)
    stack0o := stack50000o;
    // ----- copy  ----- ManualRange1.ssc(66,10)
    result := stack0o;
    goto block14620;

  block14620:
    // ----- serialized AssumeStatement  ----- ManualRange1.ssc(67,10)
    assume result != this;
    goto block14773;

  block14773:
    // ----- nop
    goto block14790;

  block14790:
    // ----- copy  ----- ManualRange1.ssc(68,17)
    stack0o := result;
    assert stack0o != null;
    return.value := stack0o;
    // ----- branch
    goto block14807;

  block14807:
    goto block15521;

  block15521:
    // ----- nop
    goto block15538;

  block15538:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
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

procedure Tools.Range$System.Int32$System.Int32(a$in: int where InRange(a$in, System.Int32), b$in: int where InRange(b$in, System.Int32)) returns ($result: ref where $IsNotNull($result, Tools.Range_Enumerable));
  free requires true;
  free requires true;
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, Tools.Range_Enumerable);
  // user-declared postconditions
  ensures $Heap[$result, Tools.Range_Enumerable.A] == a$in && $Heap[$result, Tools.Range_Enumerable.B] == b$in;
  ensures $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder && (forall $fpc: ref :: $fpc != null && old($Heap)[$fpc, $allocated] == true ==> !($Heap[$fpc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$fpc, $ownerFrame] == $Heap[$result, $ownerFrame]));
  // return value is peer consistent
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Tools.Range$System.Int32$System.Int32(a$in: int, b$in: int) returns ($result: ref)
{
  var a: int where InRange(a, System.Int32), b: int where InRange(b, System.Int32), stack0i: int, stack1i: int, stack50000o: ref, stack0o: ref, return.value: ref where $IsNotNull(return.value, Tools.Range_Enumerable), SS$Display.Return.Local: ref where $IsNotNull(SS$Display.Return.Local, Tools.Range_Enumerable);

  entry:
    a := a$in;
    b := b$in;
    goto block16252;

  block16252:
    goto block16269;

  block16269:
    // ----- copy  ----- ManualRange1.ssc(76,35)
    stack0i := a;
    // ----- copy  ----- ManualRange1.ssc(76,38)
    stack1i := b;
    // ----- new object  ----- ManualRange1.ssc(76,14)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Tools.Range_Enumerable;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- ManualRange1.ssc(76,14)
    assert stack50000o != null;
    call Tools.Range_Enumerable..ctor$System.Int32$System.Int32(stack50000o, stack0i, stack1i);
    // ----- copy  ----- ManualRange1.ssc(76,7)
    stack0o := stack50000o;
    // ----- copy  ----- ManualRange1.ssc(76,7)
    return.value := stack0o;
    // ----- branch
    goto block16286;

  block16286:
    goto block16609;

  block16609:
    // ----- nop
    goto block16626;

  block16626:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- ManualRange1.ssc(77,4)
    stack0o := return.value;
    // ----- return  ----- ManualRange1.ssc(77,4)
    $result := stack0o;
    return;

}



axiom Test <: Test;

axiom $BaseClass(Test) == System.Object;

axiom Test <: $BaseClass(Test) && AsDirectSubClass(Test, $BaseClass(Test)) == Test;

axiom !$IsImmutable(Test) && $AsMutable(Test) == Test;

axiom $IsMemberlessType(Test);

axiom (forall $U: name :: { $U <: Test } $U <: Test ==> $U == Test);

procedure Test.Main();
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



implementation Test.Main()
{
  var stack0i: int, stack1i: int, c: ref where $IsNotNull(c, Tools.Range_Enumerable), stack0o: ref, e: ref where $IsNotNull(e, Tools.Range_Enumerator), sum: int where InRange(sum, System.Int32), stack0b: bool, $Heap$block19618$LoopPreheader: [ref,<x>name]x;

  entry:
    goto block18700;

  block18700:
    goto block18717;

  block18717:
    // ----- load constant 1  ----- ManualRange1.ssc(84,47)
    stack0i := 1;
    // ----- load constant 3  ----- ManualRange1.ssc(84,50)
    stack1i := 3;
    // ----- call  ----- ManualRange1.ssc(84,7)
    call c := Tools.Range$System.Int32$System.Int32(stack0i, stack1i);
    goto block18734;

  block18734:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(85,7)
    assert $Heap[c, Tools.Range_Enumerable.A] == 1;
    goto block18887;

  block18887:
    // ----- nop
    goto block18904;

  block18904:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(86,7)
    assert $Heap[c, Tools.Range_Enumerable.B] == 3;
    goto block19057;

  block19057:
    // ----- nop
    goto block19074;

  block19074:
    // ----- call  ----- ManualRange1.ssc(87,7)
    assert c != null;
    call e := Tools.Range_Enumerable.GetEnumerator(c);
    goto block19091;

  block19091:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(88,7)
    assert $Heap[e, Tools.Range_Enumerator.A] == 1;
    goto block19244;

  block19244:
    // ----- nop
    goto block19261;

  block19261:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(89,7)
    assert $Heap[e, Tools.Range_Enumerator.B] == 3;
    goto block19414;

  block19414:
    // ----- nop
    goto block19431;

  block19431:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(90,7)
    assert $Heap[e, Tools.Range_Enumerator.Index] == -1;
    goto block19584;

  block19584:
    // ----- nop
    goto block19601;

  block19601:
    // ----- load constant 0  ----- ManualRange1.ssc(91,7)
    sum := 0;
    goto block19618$LoopPreheader;

  block19618:
    // ----- default loop invariant: allocation and ownership are stable  ----- ManualRange1.ssc(94,20)
    assume (forall $o: ref :: $Heap$block19618$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block19618$LoopPreheader[$ot, $allocated] == true && $Heap$block19618$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block19618$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block19618$LoopPreheader[$ot, $ownerFrame]) && $Heap$block19618$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- ManualRange1.ssc(94,20)
    assume (forall $o: ref :: ($Heap$block19618$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block19618$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block19618$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block19618$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- ManualRange1.ssc(94,20)
    assert (forall $o: ref :: $o != null && $Heap$block19618$LoopPreheader[$o, $allocated] == true ==> $Heap$block19618$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block19618$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(94,20)
    assert $Heap[e, Tools.Range_Enumerator.A] == 1;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(95,20)
    assert $Heap[e, Tools.Range_Enumerator.B] == 3;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(96,20)
    assert -1 <= $Heap[e, Tools.Range_Enumerator.Index];
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(97,20)
    assert $Heap[e, Tools.Range_Enumerator.Index] <= 1;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(98,20)
    assert $Heap[e, Tools.Range_Enumerator.Index] == -1 ==> sum == 0;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(99,20)
    assert $Heap[e, Tools.Range_Enumerator.Index] == 0 ==> sum == 1;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(100,20)
    assert $Heap[e, Tools.Range_Enumerator.Index] == 1 ==> sum == 3;
    // ----- serialized LoopInvariant  ----- ManualRange1.ssc(101,22)
    assert ($Heap[e, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[e, $ownerRef], $inv] <: $Heap[e, $ownerFrame]) || $Heap[$Heap[e, $ownerRef], $localinv] == $BaseClass($Heap[e, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[e, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[e, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
    goto block20638;

  block20638:
    // ----- nop
    goto block20655;

  block20655:
    // ----- call  ----- ManualRange1.ssc(92,14)
    assert e != null;
    call stack0b := Tools.Range_Enumerator.MoveNext(e);
    // ----- unary operator  ----- ManualRange1.ssc(92,14)
    // ----- branch  ----- ManualRange1.ssc(92,7)
    goto true20655to20706, false20655to20672;

  true20655to20706:
    assume !stack0b;
    goto block20706;

  false20655to20672:
    assume stack0b;
    goto block20672;

  block20706:
    goto block20723;

  block20672:
    // ----- call  ----- ManualRange1.ssc(103,17)
    assert e != null;
    call stack0i := Tools.Range_Enumerator.get_Current(e);
    // ----- binary operator  ----- ManualRange1.ssc(103,10)
    stack0i := sum + stack0i;
    // ----- copy  ----- ManualRange1.ssc(103,10)
    sum := stack0i;
    goto block20689;

  block20689:
    // ----- branch  ----- ManualRange1.ssc(104,8)
    goto block19618;

  block20723:
    // ----- serialized AssertStatement  ----- ManualRange1.ssc(105,7)
    assert sum == 3;
    goto block20876;

  block20876:
    // ----- nop
    goto block20893;

  block20893:
    goto block20910;

  block20910:
    // ----- return  ----- ManualRange1.ssc(106,4)
    return;

  block19618$LoopPreheader:
    $Heap$block19618$LoopPreheader := $Heap;
    goto block19618;

}


