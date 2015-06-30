// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo Bag7

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

const Bag.elems: <ref>name;

const Bag.count: <int>name;

const System.Collections.IList: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Runtime.InteropServices._MemberInfo: name;

const Microsoft.Contracts.GuardException: name;

const System.Reflection.MemberInfo: name;

const System.Collections.IEnumerable: name;

const System.Runtime.InteropServices._Type: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.Exception: name;

const Microsoft.Contracts.ICheckedException: name;

const Bag: name;

const System.Collections.ICollection: name;

const System.Runtime.InteropServices._Exception: name;

const System.Boolean: name;

const System.Reflection.IReflect: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.ICloneable: name;

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
    goto block5151;

  block5151:
    goto block5168;

  block5168:
    // ----- load constant 0  ----- Bag7.ssc(8,13)
    stack0i := 0;
    // ----- load field  ----- Bag7.ssc(8,18)
    assert this != null;
    stack1i := $Heap[this, Bag.count];
    // ----- binary operator  ----- Bag7.ssc(8,13)
    // ----- branch
    goto true5168to5219, false5168to5185;

  true5168to5219:
    assume stack0i > stack1i;
    goto block5219;

  false5168to5185:
    assume stack0i <= stack1i;
    goto block5185;

  block5219:
    goto block5236;

  block5185:
    // ----- load field  ----- Bag7.ssc(8,27)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- load field  ----- Bag7.ssc(8,36)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag7.ssc(8,36)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag7.ssc(8,27)
    // ----- branch
    goto true5185to5219, false5185to5202;

  true5185to5219:
    assume stack0i > stack1i;
    goto block5219;

  false5185to5202:
    assume stack0i <= stack1i;
    goto block5202;

  block5202:
    // ----- branch
    goto block5338;

  block5236:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true5236to5287, false5236to5253;

  true5236to5287:
    assume !stack0b;
    goto block5287;

  false5236to5253:
    assume stack0b;
    goto block5253;

  block5287:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block5389;

  block5253:
    assume false;
    // ----- new object  ----- Bag7.ssc(8,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Bag7.ssc(8,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- Bag7.ssc(8,3)
    stack0o := stack50000o;
    // ----- throw  ----- Bag7.ssc(8,3)
    assert stack0o != null;
    assume false;
    return;

  block5338:
    goto block5355;

  block5355:
    goto block5372;

  block5389:
    goto block5406;

  block5372:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block5389;

  block5406:
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
    goto block6086;

  block6086:
    goto block6290;

  block6290:
    // ----- nop
    goto block6307;

  block6307:
    goto block6324;

  block6324:
    goto block6341;

  block6341:
    goto block6358;

  block6358:
    // ----- array length  ----- Bag7.ssc(11,18)
    assert initialElements != null;
    stack0i := $Length(initialElements);
    // ----- store field  ----- Bag7.ssc(11,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    goto block6375;

  block6375:
    // ----- array length  ----- Bag7.ssc(12,23)
    assert initialElements != null;
    stack0i := $Length(initialElements);
    // ----- new array  ----- Bag7.ssc(12,5)
    assert 0 <= stack0i;
    havoc e;
    assume $Heap[e, $allocated] == false && $Length(e) == stack0i;
    assume $IsNotNull(e, ValueArray(System.Int32, 1));
    assume $Heap[e, $ownerRef] == e && $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[e, $inv] == ValueArray(System.Int32, 1) && $Heap[e, $localinv] == ValueArray(System.Int32, 1) && ($Heap[e, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[e, $ownerRef], $inv] <: $Heap[e, $ownerFrame]) || $Heap[$Heap[e, $ownerRef], $localinv] == $BaseClass($Heap[e, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[e, $elements], $i),int) == 0);
    $Heap[e, $allocated] := true;
    assume IsHeap($Heap);
    goto block6392;

  block6392:
    // ----- copy  ----- Bag7.ssc(13,16)
    stack0o := initialElements;
    // ----- load constant 0  ----- Bag7.ssc(13,33)
    stack1i := 0;
    // ----- copy  ----- Bag7.ssc(13,36)
    stack2o := e;
    assert stack2o != null;
    stack2o := stack2o;
    // ----- load constant 0  ----- Bag7.ssc(13,39)
    stack3i := 0;
    // ----- array length  ----- Bag7.ssc(13,42)
    assert initialElements != null;
    stack4i := $Length(initialElements);
    // ----- call  ----- Bag7.ssc(13,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- Bag7.ssc(14,18)
    stack0o := e;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- Bag7.ssc(14,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := stack0o;
    call $UpdateOwnersForRep(this, Bag, stack0o);
    assume IsHeap($Heap);
    goto block6409;

  block6409:
    // ----- call  ----- Bag7.ssc(15,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block6528;

  block6528:
    goto block6545;

  block6545:
    // ----- nop
    goto block6562;

  block6562:
    goto block6579;

  block6579:
    // ----- FrameGuard processing  ----- Bag7.ssc(16,3)
    temp0 := this;
    // ----- classic pack  ----- Bag7.ssc(16,3)
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
    goto block7531;

  block7531:
    goto block7956;

  block7956:
    // ----- nop
    goto block7973;

  block7973:
    goto block7990;

  block7990:
    goto block8007;

  block8007:
    goto block8024;

  block8024:
    // ----- store field  ----- Bag7.ssc(22,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := howMany;
    assume IsHeap($Heap);
    goto block8041;

  block8041:
    // ----- copy  ----- Bag7.ssc(23,23)
    stack0i := howMany;
    // ----- new array  ----- Bag7.ssc(23,5)
    assert 0 <= stack0i;
    havoc e;
    assume $Heap[e, $allocated] == false && $Length(e) == stack0i;
    assume $IsNotNull(e, ValueArray(System.Int32, 1));
    assume $Heap[e, $ownerRef] == e && $Heap[e, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[e, $inv] == ValueArray(System.Int32, 1) && $Heap[e, $localinv] == ValueArray(System.Int32, 1) && ($Heap[e, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[e, $ownerRef], $inv] <: $Heap[e, $ownerFrame]) || $Heap[$Heap[e, $ownerRef], $localinv] == $BaseClass($Heap[e, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[e, $elements], $i),int) == 0);
    $Heap[e, $allocated] := true;
    assume IsHeap($Heap);
    goto block8058;

  block8058:
    // ----- copy  ----- Bag7.ssc(24,16)
    stack0o := initialElements;
    // ----- copy  ----- Bag7.ssc(24,33)
    stack1i := start;
    // ----- copy  ----- Bag7.ssc(24,40)
    stack2o := e;
    assert stack2o != null;
    stack2o := stack2o;
    // ----- load constant 0  ----- Bag7.ssc(24,43)
    stack3i := 0;
    // ----- copy  ----- Bag7.ssc(24,46)
    stack4i := howMany;
    // ----- call  ----- Bag7.ssc(24,5)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- copy  ----- Bag7.ssc(25,18)
    stack0o := e;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- Bag7.ssc(25,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := stack0o;
    call $UpdateOwnersForRep(this, Bag, stack0o);
    assume IsHeap($Heap);
    goto block8075;

  block8075:
    // ----- call  ----- Bag7.ssc(26,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block8194;

  block8194:
    goto block8211;

  block8211:
    // ----- nop
    goto block8228;

  block8228:
    goto block8245;

  block8245:
    // ----- FrameGuard processing  ----- Bag7.ssc(27,3)
    temp0 := this;
    // ----- classic pack  ----- Bag7.ssc(27,3)
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
  // user-declared preconditions
  requires 0 < $Heap[this, Bag.count];
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
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local10693: ref where $Is(local10693, System.Exception), m: int where InRange(m, System.Int32), mindex: int where InRange(mindex, System.Int32), i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, stack1i: int, local10761: int where InRange(local10761, System.Int32), stack2o: ref, stack3i: int, stack2i: int, local10812: int where InRange(local10812, System.Int32), return.value: int where InRange(return.value, System.Int32), stack0s: struct, SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block9809$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    goto block9367;

  block9367:
    goto block9724;

  block9724:
    // ----- nop
    goto block9741;

  block9741:
    // ----- FrameGuard processing  ----- Bag7.ssc(32,13)
    temp0 := this;
    // ----- load token  ----- Bag7.ssc(32,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag7.ssc(32,13)
    stack1o := TypeObject(Bag);
    // ----- local unpack  ----- Bag7.ssc(32,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Bag && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local10693 := null;
    goto block9758;

  block9758:
    // ----- load constant 2147483647  ----- Bag7.ssc(34,7)
    m := int#2147483647;
    goto block9775;

  block9775:
    // ----- load constant 0  ----- Bag7.ssc(35,7)
    mindex := 0;
    goto block9792;

  block9792:
    // ----- load constant 0  ----- Bag7.ssc(36,12)
    i := 0;
    goto block9809$LoopPreheader;

  block9809:
    // ----- default loop invariant: allocation and ownership are stable  ----- Bag7.ssc(36,27)
    assume (forall $o: ref :: $Heap$block9809$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block9809$LoopPreheader[$ot, $allocated] == true && $Heap$block9809$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block9809$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block9809$LoopPreheader[$ot, $ownerFrame]) && $Heap$block9809$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Bag7.ssc(36,27)
    assume (forall $o: ref :: ($Heap$block9809$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block9809$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block9809$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block9809$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Bag7.ssc(36,27)
    assert (forall $o: ref :: $o != null && $Heap$block9809$LoopPreheader[$o, $allocated] == true ==> $Heap$block9809$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block9809$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- Bag7.ssc(36,27)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- binary operator  ----- Bag7.ssc(36,23)
    // ----- branch  ----- Bag7.ssc(36,23)
    goto true9809to9945, false9809to9826;

  true9809to9945:
    assume i >= stack0i;
    goto block9945;

  false9809to9826:
    assume i < stack0i;
    goto block9826;

  block9945:
    goto block9962;

  block9826:
    // ----- load field  ----- Bag7.ssc(37,13)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag7.ssc(37,19)
    stack1i := i;
    // ----- load element  ----- Bag7.ssc(37,13)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    stack0i := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    // ----- binary operator  ----- Bag7.ssc(37,13)
    // ----- branch  ----- Bag7.ssc(37,9)
    goto true9826to9860, false9826to9843;

  true9826to9860:
    assume stack0i >= m;
    goto block9860;

  false9826to9843:
    assume stack0i < m;
    goto block9843;

  block9860:
    goto block9877;

  block9843:
    // ----- copy  ----- Bag7.ssc(38,11)
    mindex := i;
    // ----- load field  ----- Bag7.ssc(39,15)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag7.ssc(39,21)
    stack1i := i;
    // ----- load element  ----- Bag7.ssc(39,11)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    m := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    goto block9860;

  block9962:
    // ----- load field  ----- Bag7.ssc(42,7)
    assert this != null;
    local10761 := $Heap[this, Bag.count];
    // ----- load constant 1  ----- Bag7.ssc(42,7)
    stack0i := 1;
    // ----- binary operator  ----- Bag7.ssc(42,7)
    stack0i := local10761 - stack0i;
    // ----- store field  ----- Bag7.ssc(42,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- Bag7.ssc(42,7)
    stack0i := local10761;
    goto block9979;

  block9877:
    goto block9894;

  block9979:
    // ----- nop  ----- Bag7.ssc(42,7)
    // ----- load field  ----- Bag7.ssc(43,7)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- copy  ----- Bag7.ssc(43,13)
    stack1i := mindex;
    // ----- load field  ----- Bag7.ssc(43,23)
    assert this != null;
    stack2o := $Heap[this, Bag.elems];
    // ----- load field  ----- Bag7.ssc(43,29)
    assert this != null;
    stack3i := $Heap[this, Bag.count];
    // ----- load element  ----- Bag7.ssc(43,23)
    assert stack2o != null;
    assert 0 <= stack3i;
    assert stack3i < $Length(stack2o);
    stack2i := cast(ValueArrayGet($Heap[stack2o, $elements], stack3i),int);
    // ----- store element  ----- Bag7.ssc(43,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    $Heap[stack0o, $elements] := ValueArraySet($Heap[stack0o, $elements], stack1i, stack2i);
    assume IsHeap($Heap);
    goto block9996;

  block9894:
    // ----- copy  ----- Bag7.ssc(36,34)
    local10812 := i;
    // ----- load constant 1  ----- Bag7.ssc(36,34)
    stack0i := 1;
    // ----- binary operator  ----- Bag7.ssc(36,34)
    stack0i := local10812 + stack0i;
    // ----- copy  ----- Bag7.ssc(36,34)
    i := stack0i;
    // ----- copy  ----- Bag7.ssc(36,34)
    stack0i := local10812;
    goto block9911;

  block9996:
    // ----- copy  ----- Bag7.ssc(44,7)
    return.value := m;
    // ----- branch
    goto block10183;

  block9911:
    // ----- nop  ----- Bag7.ssc(36,34)
    goto block9928;

  block10183:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true10183to10285, false10183to10200;

  true10183to10285:
    assume local10693 == stack0o;
    goto block10285;

  false10183to10200:
    assume local10693 != stack0o;
    goto block10200;

  block10285:
    goto block10302;

  block10200:
    // ----- is instance
    // ----- branch
    goto true10200to10285, false10200to10217;

  block9928:
    // ----- branch
    goto block9809;

  true10200to10285:
    assume $As(local10693, Microsoft.Contracts.ICheckedException) != null;
    goto block10285;

  false10200to10217:
    assume $As(local10693, Microsoft.Contracts.ICheckedException) == null;
    goto block10217;

  block10217:
    // ----- branch
    goto block10234;

  block10302:
    // ----- load token  ----- Bag7.ssc(45,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag7.ssc(45,5)
    stack0o := TypeObject(Bag);
    // ----- local pack  ----- Bag7.ssc(45,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block10234;

  block10234:
    goto block10251;

  block10251:
    goto block10268;

  block10268:
    // ----- nop
    // ----- branch
    goto block10149;

  block10149:
    goto block10166;

  block10166:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

  block9809$LoopPreheader:
    $Heap$block9809$LoopPreheader := $Heap;
    goto block9809;

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
  var x: int where InRange(x, System.Int32), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local12546: ref where $Is(local12546, System.Exception), stack0i: int, stack1i: int, stack0b: bool, b: ref where $IsNotNull(b, ValueArray(System.Int32, 1)), stack0o: ref, stack2o: ref, stack3i: int, stack4o: ref, stack4i: int, local12580: int where InRange(local12580, System.Int32), stack0s: struct;

  entry:
    assume $IsNotNull(this, Bag);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block11577;

  block11577:
    goto block11832;

  block11832:
    // ----- nop
    goto block11849;

  block11849:
    // ----- FrameGuard processing  ----- Bag7.ssc(50,13)
    temp0 := this;
    // ----- load token  ----- Bag7.ssc(50,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag7.ssc(50,13)
    stack1o := TypeObject(Bag);
    // ----- local unpack  ----- Bag7.ssc(50,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Bag && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local12546 := null;
    goto block11866;

  block11866:
    // ----- load field  ----- Bag7.ssc(52,11)
    assert this != null;
    stack0i := $Heap[this, Bag.count];
    // ----- load field  ----- Bag7.ssc(52,20)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag7.ssc(52,20)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag7.ssc(52,11)
    // ----- branch  ----- Bag7.ssc(52,7)
    goto true11866to11917, false11866to11883;

  true11866to11917:
    assume stack0i != stack1i;
    goto block11917;

  false11866to11883:
    assume stack0i == stack1i;
    goto block11883;

  block11917:
    goto block11934;

  block11883:
    // ----- load constant 2  ----- Bag7.ssc(54,28)
    stack0i := 2;
    // ----- load field  ----- Bag7.ssc(54,30)
    assert this != null;
    stack1o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag7.ssc(54,30)
    assert stack1o != null;
    stack1i := $Length(stack1o);
    // ----- binary operator  ----- Bag7.ssc(54,28)
    stack0i := stack0i * stack1i;
    // ----- new array  ----- Bag7.ssc(54,9)
    assert 0 <= stack0i;
    havoc b;
    assume $Heap[b, $allocated] == false && $Length(b) == stack0i;
    assume $IsNotNull(b, ValueArray(System.Int32, 1));
    assume $Heap[b, $ownerRef] == b && $Heap[b, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[b, $inv] == ValueArray(System.Int32, 1) && $Heap[b, $localinv] == ValueArray(System.Int32, 1) && ($Heap[b, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b, $ownerRef], $inv] <: $Heap[b, $ownerFrame]) || $Heap[$Heap[b, $ownerRef], $localinv] == $BaseClass($Heap[b, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[b, $elements], $i),int) == 0);
    $Heap[b, $allocated] := true;
    assume IsHeap($Heap);
    goto block11900;

  block11900:
    // ----- load field  ----- Bag7.ssc(55,20)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- load constant 0  ----- Bag7.ssc(55,27)
    stack1i := 0;
    // ----- copy  ----- Bag7.ssc(55,30)
    stack2o := b;
    // ----- load constant 0  ----- Bag7.ssc(55,33)
    stack3i := 0;
    // ----- load field  ----- Bag7.ssc(55,36)
    assert this != null;
    stack4o := $Heap[this, Bag.elems];
    // ----- array length  ----- Bag7.ssc(55,36)
    assert stack4o != null;
    stack4i := $Length(stack4o);
    // ----- call  ----- Bag7.ssc(55,9)
    call System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2o, stack3i, stack4i);
    // ----- store field  ----- Bag7.ssc(56,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    assert $Heap[b, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[b, $ownerRef] == this && $Heap[b, $ownerFrame] == Bag);
    $Heap[this, Bag.elems] := b;
    call $UpdateOwnersForRep(this, Bag, b);
    assume IsHeap($Heap);
    goto block11917;

  block11934:
    goto block11951;

  block11951:
    // ----- load field  ----- Bag7.ssc(58,7)
    assert this != null;
    stack0o := $Heap[this, Bag.elems];
    // ----- load field  ----- Bag7.ssc(58,13)
    assert this != null;
    stack1i := $Heap[this, Bag.count];
    // ----- store element  ----- Bag7.ssc(58,7)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    $Heap[stack0o, $elements] := ValueArraySet($Heap[stack0o, $elements], stack1i, x);
    assume IsHeap($Heap);
    goto block11968;

  block11968:
    // ----- load field  ----- Bag7.ssc(59,7)
    assert this != null;
    local12580 := $Heap[this, Bag.count];
    // ----- load constant 1  ----- Bag7.ssc(59,7)
    stack0i := 1;
    // ----- binary operator  ----- Bag7.ssc(59,7)
    stack0i := local12580 + stack0i;
    // ----- store field  ----- Bag7.ssc(59,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Bag) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Bag.count] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- Bag7.ssc(59,7)
    stack0i := local12580;
    goto block11985;

  block11985:
    // ----- nop  ----- Bag7.ssc(59,7)
    // ----- branch
    goto block12155;

  block12155:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true12155to12257, false12155to12172;

  true12155to12257:
    assume local12546 == stack0o;
    goto block12257;

  false12155to12172:
    assume local12546 != stack0o;
    goto block12172;

  block12257:
    goto block12274;

  block12172:
    // ----- is instance
    // ----- branch
    goto true12172to12257, false12172to12189;

  true12172to12257:
    assume $As(local12546, Microsoft.Contracts.ICheckedException) != null;
    goto block12257;

  false12172to12189:
    assume $As(local12546, Microsoft.Contracts.ICheckedException) == null;
    goto block12189;

  block12189:
    // ----- branch
    goto block12206;

  block12274:
    // ----- load token  ----- Bag7.ssc(60,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Bag);
    // ----- statically resolved GetTypeFromHandle call  ----- Bag7.ssc(60,5)
    stack0o := TypeObject(Bag);
    // ----- local pack  ----- Bag7.ssc(60,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, Bag.count] && $Heap[temp0, Bag.count] <= $Length($Heap[temp0, Bag.elems]);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Bag ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block12206;

  block12206:
    goto block12223;

  block12223:
    goto block12240;

  block12240:
    // ----- nop
    // ----- branch
    goto block12104;

  block12104:
    goto block12121;

  block12121:
    goto block12138;

  block12138:
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
    goto block13107;

  block13107:
    goto block13226;

  block13226:
    // ----- nop
    goto block13243;

  block13243:
    goto block13260;

  block13260:
    // ----- return
    return;

}


