// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo Bag5

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

const Bag.count: <int>name;

const Bag.elems: <ref>name;

const System.Collections.ICollection: name;

const Microsoft.Contracts.GuardException: name;

const Bag: name;

const System.ICloneable: name;

const Microsoft.Contracts.ICheckedException: name;

const System.Runtime.InteropServices._Exception: name;

const System.Exception: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Runtime.InteropServices._Type: name;

const System.Boolean: name;

const System.Reflection.IReflect: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Reflection.MemberInfo: name;

const System.Collections.IList: name;

const System.Collections.IEnumerable: name;

const Microsoft.Contracts.ObjectInvariantException: name;

axiom !IsStaticField(Bag.count);

axiom IsDirectlyModifiableField(Bag.count);

axiom DeclType(Bag.count) == Bag;

axiom AsRangeField(Bag.count, System.Int32) == Bag.count;

axiom !IsStaticField(Bag.elems);

axiom IsDirectlyModifiableField(Bag.elems);

axiom AsRepField(Bag.elems, Bag) == Bag.elems;

axiom DeclType(Bag.elems) == Bag;

axiom AsNonNullRefField(Bag.elems, ValueArray(System.Int32, 1)) == Bag.elems;

axiom Bag <: Bag;

axiom $BaseClass(Bag) == System.Object;

axiom Bag <: $BaseClass(Bag) && AsDirectSubClass(Bag, $BaseClass(Bag)) == Bag;

axiom !$IsImmutable(Bag) && $AsMutable(Bag) == Bag;

axiom (forall $U: name :: { $U <: Bag } $U <: Bag ==> $U == Bag);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Bag } IsHeap($h) && $h[$oi, $inv] <: Bag && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, Bag.count] && $h[$oi, Bag.count] <= $Length($h[$oi, Bag.elems]));

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Bag.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Bag.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, stack1o: ref, stack50000o: ref, stack0o: ref, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block5083;

  block5083:
    goto block5100;

  block5100:
    // ----- load constant 0  ----- Bag5.ssc(8,13)
    stack0i := 0;
    // ----- load field  ----- Bag5.ssc(8,18)
    assert this != null;
    stack1i := $Heap[this, Bag.count];
    // ----- binary operator  ----- Bag5.ssc(8,13)
    // ----- branch
    goto true5100to5151, false5100to5117;

  true5100to5151:
    assume stack0i > stack1i;
    goto block5151;

  false5100to5117:
    assume stack0i <= stack1i;
    goto block5117;

  block5151:
    goto block5168;

  block5117:
    // ----- load field  ----- Bag5.ssc(8,27)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- load field  ----- Bag5.ssc(8,36)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag5.ssc(8,36)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag5.ssc(8,27)
    // ----- branch
    goto true5117to5151, false5117to5134;

  true5117to5151:
    assume stack0i > stack1i;
    goto block5151;

  false5117to5134:
    assume stack0i <= stack1i;
    goto block5134;

  block5134:
    // ----- branch
    goto block5270;

  block5168:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true5168to5219, false5168to5185;

  true5168to5219:
    assume !stack0b;
    goto block5219;

  false5168to5185:
    assume stack0b;
    goto block5185;

  block5219:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block5321;

  block5185:
    assume false;
    // ----- new object  ----- Bag5.ssc(8,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Bag5.ssc(8,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- Bag5.ssc(8,3)
    stack0o := stack50000o;
    // ----- throw  ----- Bag5.ssc(8,3)
    assert stack0o != null;
    assume false;
    return;

  block5270:
    goto block5287;

  block5287:
    goto block5304;

  block5321:
    goto block5338;

  block5304:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block5321;

  block5338:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
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



procedure Bag..ctor$System.Int32.array$notnull(this: ref, initialElements$in: ref where $IsNotNull(initialElements$in, ValueArray(System.Int32, 1)));
  free requires $Heap[initialElements$in, $allocated] == true;
  requires ($Heap[initialElements$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[initialElements$in, $ownerRef], $inv] <: $Heap[initialElements$in, $ownerFrame]) || $Heap[$Heap[initialElements$in, $ownerRef], $localinv] == $BaseClass($Heap[initialElements$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[initialElements$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[initialElements$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Bag && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Bag <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Bag..ctor$System.Int32.array$notnull(this: ref, initialElements$in: ref)
{
  var initialElements: ref where $IsNotNull(initialElements, ValueArray(System.Int32, 1)), stack0i: int, e: ref where $Is(e, ValueArray(System.Int32, 1)), stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, temp0: ref;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    initialElements := initialElements$in;
    assume $Heap[this, Bag.count] == 0;
    goto block6018;

  block6018:
    goto block6222;

  block6222:
    // ----- nop
    goto block6239;

  block6239:
    goto block6256;

  block6256:
    goto block6273;

  block6273:
    goto block6290;

  block6290:
    // ----- array length  ----- Bag5.ssc(11,18)
    assert initialElements != null;
    stack0i := $Length(initialElements);
    // ----- store field  ----- Bag5.ssc(11,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    goto block6307;

  block6307:
    // ----- array length  ----- Bag5.ssc(12,23)
    assert initialElements != null;
    stack0i := $Length(initialElements);
    // ----- new array  ----- Bag5.ssc(12,5)
    assert 0 <= stack0i;
    havoc e;
    assume $Heap[e, $allocated] == false && $Length(e) == stack0i;
    assume $IsNotNull(e, ValueArray(System.Int32, 1));
    assume $Heap[e, $ownerRef] == e && $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[e, $inv] == ValueArray(System.Int32, 1) && $Heap[e, $localinv] == ValueArray(System.Int32, 1) && ($Heap[e, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[e, $ownerRef], $inv] <: $Heap[e, $ownerFrame]) || $Heap[$Heap[e, $ownerRef], $localinv] == $BaseClass($Heap[e, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[e, $elements], $i),int) == 0);
    $Heap[e, $allocated] := true;
    assume IsHeap($Heap);
    goto block6324;

  block6324:
    // ----- copy  ----- Bag5.ssc(13,16)
    stack0o := initialElements;
    // ----- load constant 0  ----- Bag5.ssc(13,33)
    stack1i := 0;
    // ----- copy  ----- Bag5.ssc(13,36)
    stack2o := e;
    assert stack2o != null;
    stack2o := stack2o;
    // ----- load constant 0  ----- Bag5.ssc(13,39)
    stack3i := 0;
    // ----- array length  ----- Bag5.ssc(13,42)
    assert initialElements != null;
    stack4i := $Length(initialElements);
    // ----- call  ----- Bag5.ssc(13,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- Bag5.ssc(14,18)
    stack0o := e;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- Bag5.ssc(14,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := stack0o;
    call $UpdateOwnersForRep(this, Bag, stack0o);
    assume IsHeap($Heap);
    goto block6341;

  block6341:
    // ----- call  ----- Bag5.ssc(15,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block6460;

  block6460:
    goto block6477;

  block6477:
    // ----- nop
    goto block6494;

  block6494:
    goto block6511;

  block6511:
    // ----- FrameGuard processing  ----- Bag5.ssc(16,3)
    temp0 := this;
    // ----- classic pack  ----- Bag5.ssc(16,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Bag;
    assume IsHeap($Heap);
    // ----- return
    return;

}



axiom System.Array <: System.Array;

axiom $BaseClass(System.Array) == System.Object;

axiom System.Array <: $BaseClass(System.Array) && AsDirectSubClass(System.Array, $BaseClass(System.Array)) == System.Array;

axiom !$IsImmutable(System.Array) && $AsMutable(System.Array) == System.Array;

axiom System.ICloneable <: System.Object;

axiom $IsMemberlessType(System.ICloneable);

axiom System.Array <: System.ICloneable;

axiom System.Collections.IList <: System.Object;

axiom System.Collections.ICollection <: System.Object;

axiom System.Collections.IEnumerable <: System.Object;

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom System.Collections.ICollection <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.ICollection);

axiom System.Collections.IList <: System.Collections.ICollection;

axiom System.Collections.IList <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.IList);

axiom System.Array <: System.Collections.IList;

axiom System.Array <: System.Collections.ICollection;

axiom System.Array <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Array);

procedure System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(sourceArray$in: ref where $IsNotNull(sourceArray$in, System.Array), sourceIndex$in: int where InRange(sourceIndex$in, System.Int32), destinationArray$in: ref where $IsNotNull(destinationArray$in, System.Array), destinationIndex$in: int where InRange(destinationIndex$in, System.Int32), length$in: int where InRange(length$in, System.Int32));
  free requires $Heap[sourceArray$in, $allocated] == true;
  free requires true;
  free requires $Heap[destinationArray$in, $allocated] == true;
  free requires true;
  free requires true;
  // user-declared preconditions
  requires sourceArray$in != null;
  requires destinationArray$in != null;
  requires $Rank(sourceArray$in) == $Rank(destinationArray$in);
  requires sourceIndex$in >= $LBound(sourceArray$in, 0);
  requires destinationIndex$in >= $LBound(destinationArray$in, 0);
  requires length$in >= 0;
  requires sourceIndex$in + length$in <= $LBound(sourceArray$in, 0) + $Length(sourceArray$in);
  requires destinationIndex$in + length$in <= $LBound(destinationArray$in, 0) + $Length(destinationArray$in);
  requires ($Heap[sourceArray$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[sourceArray$in, $ownerRef], $inv] <: $Heap[sourceArray$in, $ownerFrame]) || $Heap[$Heap[sourceArray$in, $ownerRef], $localinv] == $BaseClass($Heap[sourceArray$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[sourceArray$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[sourceArray$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[destinationArray$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[destinationArray$in, $ownerRef], $inv] <: $Heap[destinationArray$in, $ownerFrame]) || $Heap[$Heap[destinationArray$in, $ownerRef], $localinv] == $BaseClass($Heap[destinationArray$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[destinationArray$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[destinationArray$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



procedure Bag..ctor$System.Int32.array$notnull$System.Int32$System.Int32(this: ref, initialElements$in: ref where $IsNotNull(initialElements$in, ValueArray(System.Int32, 1)), start$in: int where InRange(start$in, System.Int32), howMany$in: int where InRange(howMany$in, System.Int32));
  free requires $Heap[initialElements$in, $allocated] == true;
  free requires true;
  free requires true;
  // user-declared preconditions
  requires 0 <= start$in && 0 <= howMany$in;
  requires start$in + howMany$in <= $Length(initialElements$in);
  requires ($Heap[initialElements$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[initialElements$in, $ownerRef], $inv] <: $Heap[initialElements$in, $ownerFrame]) || $Heap[$Heap[initialElements$in, $ownerRef], $localinv] == $BaseClass($Heap[initialElements$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[initialElements$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[initialElements$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Bag && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Bag <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Bag..ctor$System.Int32.array$notnull$System.Int32$System.Int32(this: ref, initialElements$in: ref, start$in: int, howMany$in: int)
{
  var initialElements: ref where $IsNotNull(initialElements, ValueArray(System.Int32, 1)), start: int where InRange(start, System.Int32), howMany: int where InRange(howMany, System.Int32), stack0i: int, e: ref where $Is(e, ValueArray(System.Int32, 1)), stack0o: ref, stack1i: int, stack2o: ref, stack3i: int, stack4i: int, temp0: ref;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    initialElements := initialElements$in;
    start := start$in;
    howMany := howMany$in;
    assume $Heap[this, Bag.count] == 0;
    goto block7463;

  block7463:
    goto block7888;

  block7888:
    // ----- nop
    goto block7905;

  block7905:
    goto block7922;

  block7922:
    goto block7939;

  block7939:
    goto block7956;

  block7956:
    // ----- store field  ----- Bag5.ssc(22,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := howMany;
    assume IsHeap($Heap);
    goto block7973;

  block7973:
    // ----- copy  ----- Bag5.ssc(23,23)
    stack0i := howMany;
    // ----- new array  ----- Bag5.ssc(23,5)
    assert 0 <= stack0i;
    havoc e;
    assume $Heap[e, $allocated] == false && $Length(e) == stack0i;
    assume $IsNotNull(e, ValueArray(System.Int32, 1));
    assume $Heap[e, $ownerRef] == e && $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[e, $inv] == ValueArray(System.Int32, 1) && $Heap[e, $localinv] == ValueArray(System.Int32, 1) && ($Heap[e, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[e, $ownerRef], $inv] <: $Heap[e, $ownerFrame]) || $Heap[$Heap[e, $ownerRef], $localinv] == $BaseClass($Heap[e, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[e, $elements], $i),int) == 0);
    $Heap[e, $allocated] := true;
    assume IsHeap($Heap);
    goto block7990;

  block7990:
    // ----- copy  ----- Bag5.ssc(24,16)
    stack0o := initialElements;
    // ----- copy  ----- Bag5.ssc(24,33)
    stack1i := start;
    // ----- copy  ----- Bag5.ssc(24,40)
    stack2o := e;
    assert stack2o != null;
    stack2o := stack2o;
    // ----- load constant 0  ----- Bag5.ssc(24,43)
    stack3i := 0;
    // ----- copy  ----- Bag5.ssc(24,46)
    stack4i := howMany;
    // ----- call  ----- Bag5.ssc(24,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- Bag5.ssc(25,18)
    stack0o := e;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- Bag5.ssc(25,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := stack0o;
    call $UpdateOwnersForRep(this, Bag, stack0o);
    assume IsHeap($Heap);
    goto block8007;

  block8007:
    // ----- call  ----- Bag5.ssc(26,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block8126;

  block8126:
    goto block8143;

  block8143:
    // ----- nop
    goto block8160;

  block8160:
    goto block8177;

  block8177:
    // ----- FrameGuard processing  ----- Bag5.ssc(27,3)
    temp0 := this;
    // ----- classic pack  ----- Bag5.ssc(27,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Bag;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure Bag.RemoveMin(this: ref) returns ($result: int where InRange($result, System.Int32));
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



implementation Bag.RemoveMin(this: ref) returns ($result: int)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local10438: ref where $Is(local10438, System.Exception), m: int where InRange(m, System.Int32), mindex: int where InRange(mindex, System.Int32), i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, stack1i: int, local10506: int where InRange(local10506, System.Int32), stack2o: ref, stack3i: int, stack2i: int, return.value: int where InRange(return.value, System.Int32), local10557: int where InRange(local10557, System.Int32), stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block9554$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    goto block9214;

  block9214:
    goto block9469;

  block9469:
    // ----- nop
    goto block9486;

  block9486:
    // ----- FrameGuard processing  ----- Bag5.ssc(31,13)
    temp0 := this;
    // ----- load token  ----- Bag5.ssc(31,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag5.ssc(31,13)
    stack1o := TypeObject(Bag);
    // ----- local unpack  ----- Bag5.ssc(31,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Bag && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local10438 := null;
    goto block9503;

  block9503:
    // ----- load constant 2147483647  ----- Bag5.ssc(33,7)
    m := int#2147483647;
    goto block9520;

  block9520:
    // ----- load constant 0  ----- Bag5.ssc(34,7)
    mindex := 0;
    goto block9537;

  block9537:
    // ----- load constant 0  ----- Bag5.ssc(35,12)
    i := 0;
    goto block9554$LoopPreheader;

  block9554:
    // ----- default loop invariant: allocation and ownership are stable  ----- Bag5.ssc(35,27)
    assume (forall $o: ref :: $Heap$block9554$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block9554$LoopPreheader[$ot, $allocated] == true && $Heap$block9554$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block9554$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block9554$LoopPreheader[$ot, $ownerFrame]) && $Heap$block9554$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Bag5.ssc(35,27)
    assume (forall $o: ref :: ($Heap$block9554$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block9554$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block9554$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block9554$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Bag5.ssc(35,27)
    assert (forall $o: ref :: $o != null && $Heap$block9554$LoopPreheader[$o, $allocated] == true ==> $Heap$block9554$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block9554$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- Bag5.ssc(35,27)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- binary operator  ----- Bag5.ssc(35,23)
    // ----- branch  ----- Bag5.ssc(35,23)
    goto true9554to9690, false9554to9571;

  true9554to9690:
    assume i >= stack0i;
    goto block9690;

  false9554to9571:
    assume i < stack0i;
    goto block9571;

  block9690:
    goto block9707;

  block9571:
    // ----- load field  ----- Bag5.ssc(36,13)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag5.ssc(36,19)
    stack1i := i;
    // ----- load element  ----- Bag5.ssc(36,13)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0i := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    // ----- binary operator  ----- Bag5.ssc(36,13)
    // ----- branch  ----- Bag5.ssc(36,9)
    goto true9571to9605, false9571to9588;

  true9571to9605:
    assume stack0i >= m;
    goto block9605;

  false9571to9588:
    assume stack0i < m;
    goto block9588;

  block9605:
    goto block9622;

  block9588:
    // ----- copy  ----- Bag5.ssc(37,11)
    mindex := i;
    // ----- load field  ----- Bag5.ssc(38,15)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag5.ssc(38,21)
    stack1i := i;
    // ----- load element  ----- Bag5.ssc(38,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    m := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    goto block9605;

  block9707:
    // ----- load field  ----- Bag5.ssc(41,7)
    assert this != null;
    local10506 := $Heap[this, Bag.count];
    // ----- load constant 1  ----- Bag5.ssc(41,7)
    stack0i := 1;
    // ----- binary operator  ----- Bag5.ssc(41,7)
    stack0i := local10506 - stack0i;
    // ----- store field  ----- Bag5.ssc(41,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- Bag5.ssc(41,7)
    stack0i := local10506;
    goto block9724;

  block9724:
    // ----- nop  ----- Bag5.ssc(41,7)
    // ----- load field  ----- Bag5.ssc(42,7)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag5.ssc(42,13)
    stack1i := mindex;
    // ----- load field  ----- Bag5.ssc(42,23)
    assert this != null;
    stack2o := $Heap[this, Bag.elems];
    // ----- load field  ----- Bag5.ssc(42,29)
    assert this != null;
    stack3i := $Heap[this, Bag.count];
    // ----- load element  ----- Bag5.ssc(42,23)
    assert stack2o != null;
    assert 0 <= stack3i;
    assert stack3i < $Length(stack2o);
    stack2i := cast(ValueArrayGet($Heap[stack2o, $elements], stack3i),int);
    // ----- store element  ----- Bag5.ssc(42,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    $Heap[stack0o, $elements] := ValueArraySet($Heap[stack0o, $elements], stack1i, stack2i);
    assume IsHeap($Heap);
    goto block9741;

  block9622:
    goto block9639;

  block9741:
    // ----- copy  ----- Bag5.ssc(43,7)
    return.value := m;
    // ----- branch
    goto block9928;

  block9639:
    // ----- copy  ----- Bag5.ssc(35,34)
    local10557 := i;
    // ----- load constant 1  ----- Bag5.ssc(35,34)
    stack0i := 1;
    // ----- binary operator  ----- Bag5.ssc(35,34)
    stack0i := local10557 + stack0i;
    // ----- copy  ----- Bag5.ssc(35,34)
    i := stack0i;
    // ----- copy  ----- Bag5.ssc(35,34)
    stack0i := local10557;
    goto block9656;

  block9928:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9928to10030, false9928to9945;

  true9928to10030:
    assume local10438 == stack0o;
    goto block10030;

  false9928to9945:
    assume local10438 != stack0o;
    goto block9945;

  block10030:
    goto block10047;

  block9945:
    // ----- is instance
    // ----- branch
    goto true9945to10030, false9945to9962;

  block9656:
    // ----- nop  ----- Bag5.ssc(35,34)
    goto block9673;

  true9945to10030:
    assume $As(local10438, Microsoft.Contracts.ICheckedException) != null;
    goto block10030;

  false9945to9962:
    assume $As(local10438, Microsoft.Contracts.ICheckedException) == null;
    goto block9962;

  block9962:
    // ----- branch
    goto block9979;

  block9673:
    // ----- branch
    goto block9554;

  block10047:
    // ----- load token  ----- Bag5.ssc(44,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag5.ssc(44,5)
    stack0o := TypeObject(Bag);
    // ----- local pack  ----- Bag5.ssc(44,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block9979;

  block9979:
    goto block9996;

  block9996:
    goto block10013;

  block10013:
    // ----- nop
    // ----- branch
    goto block9894;

  block9894:
    goto block9911;

  block9911:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

  block9554$LoopPreheader:
    $Heap$block9554$LoopPreheader := $Heap;
    goto block9554;

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

procedure Bag.Add$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
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



implementation Bag.Add$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local12291: ref where $Is(local12291, System.Exception), stack0i: int, stack1i: int, stack0b: bool, b: ref where $IsNotNull(b, ValueArray(System.Int32, 1)), stack0o: ref, stack2o: ref, stack3i: int, stack4o: ref, stack4i: int, local12325: int where InRange(local12325, System.Int32), stack0s: struct;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block11322;

  block11322:
    goto block11577;

  block11577:
    // ----- nop
    goto block11594;

  block11594:
    // ----- FrameGuard processing  ----- Bag5.ssc(49,13)
    temp0 := this;
    // ----- load token  ----- Bag5.ssc(49,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag5.ssc(49,13)
    stack1o := TypeObject(Bag);
    // ----- local unpack  ----- Bag5.ssc(49,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Bag && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local12291 := null;
    goto block11611;

  block11611:
    // ----- load field  ----- Bag5.ssc(51,11)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- load field  ----- Bag5.ssc(51,20)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag5.ssc(51,20)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag5.ssc(51,11)
    // ----- branch  ----- Bag5.ssc(51,7)
    goto true11611to11662, false11611to11628;

  true11611to11662:
    assume stack0i != stack1i;
    goto block11662;

  false11611to11628:
    assume stack0i == stack1i;
    goto block11628;

  block11662:
    goto block11679;

  block11628:
    // ----- load constant 2  ----- Bag5.ssc(53,28)
    stack0i := 2;
    // ----- load field  ----- Bag5.ssc(53,30)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag5.ssc(53,30)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag5.ssc(53,28)
    stack0i := stack0i * stack1i;
    // ----- new array  ----- Bag5.ssc(53,9)
    assert 0 <= stack0i;
    havoc b;
    assume $Heap[b, $allocated] == false && $Length(b) == stack0i;
    assume $IsNotNull(b, ValueArray(System.Int32, 1));
    assume $Heap[b, $ownerRef] == b && $Heap[b, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[b, $inv] == ValueArray(System.Int32, 1) && $Heap[b, $localinv] == ValueArray(System.Int32, 1) && ($Heap[b, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b, $ownerRef], $inv] <: $Heap[b, $ownerFrame]) || $Heap[$Heap[b, $ownerRef], $localinv] == $BaseClass($Heap[b, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[b, $elements], $i),int) == 0);
    $Heap[b, $allocated] := true;
    assume IsHeap($Heap);
    goto block11645;

  block11645:
    // ----- load field  ----- Bag5.ssc(54,20)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- load constant 0  ----- Bag5.ssc(54,27)
    stack1i := 0;
    // ----- copy  ----- Bag5.ssc(54,30)
    stack2o := b;
    // ----- load constant 0  ----- Bag5.ssc(54,33)
    stack3i := 0;
    // ----- load field  ----- Bag5.ssc(54,36)
    assert this != null;
    stack4o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag5.ssc(54,36)
    assert stack4o != null;
    stack4i := $Length(stack4o);
    // ----- call  ----- Bag5.ssc(54,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- store field  ----- Bag5.ssc(55,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[b, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[b, $ownerRef] == this && $Heap[b, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := b;
    call $UpdateOwnersForRep(this, Bag, b);
    assume IsHeap($Heap);
    goto block11662;

  block11679:
    goto block11696;

  block11696:
    // ----- load field  ----- Bag5.ssc(57,7)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- load field  ----- Bag5.ssc(57,13)
    assert this != null;
    stack1i := $Heap[this, Bag.count];
    // ----- store element  ----- Bag5.ssc(57,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    $Heap[stack0o, $elements] := ValueArraySet($Heap[stack0o, $elements], stack1i, x);
    assume IsHeap($Heap);
    goto block11713;

  block11713:
    // ----- load field  ----- Bag5.ssc(58,7)
    assert this != null;
    local12325 := $Heap[this, Bag.count];
    // ----- load constant 1  ----- Bag5.ssc(58,7)
    stack0i := 1;
    // ----- binary operator  ----- Bag5.ssc(58,7)
    stack0i := local12325 + stack0i;
    // ----- store field  ----- Bag5.ssc(58,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- Bag5.ssc(58,7)
    stack0i := local12325;
    goto block11730;

  block11730:
    // ----- nop  ----- Bag5.ssc(58,7)
    // ----- branch
    goto block11900;

  block11900:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11900to12002, false11900to11917;

  true11900to12002:
    assume local12291 == stack0o;
    goto block12002;

  false11900to11917:
    assume local12291 != stack0o;
    goto block11917;

  block12002:
    goto block12019;

  block11917:
    // ----- is instance
    // ----- branch
    goto true11917to12002, false11917to11934;

  true11917to12002:
    assume $As(local12291, Microsoft.Contracts.ICheckedException) != null;
    goto block12002;

  false11917to11934:
    assume $As(local12291, Microsoft.Contracts.ICheckedException) == null;
    goto block11934;

  block11934:
    // ----- branch
    goto block11951;

  block12019:
    // ----- load token  ----- Bag5.ssc(59,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag5.ssc(59,5)
    stack0o := TypeObject(Bag);
    // ----- local pack  ----- Bag5.ssc(59,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block11951;

  block11951:
    goto block11968;

  block11968:
    goto block11985;

  block11985:
    // ----- nop
    // ----- branch
    goto block11849;

  block11849:
    goto block11866;

  block11866:
    goto block11883;

  block11883:
    // ----- return
    return;

}



procedure Bag..cctor();
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



implementation Bag..cctor()
{

  entry:
    goto block12852;

  block12852:
    goto block12971;

  block12971:
    // ----- nop
    goto block12988;

  block12988:
    goto block13005;

  block13005:
    // ----- return
    return;

}


