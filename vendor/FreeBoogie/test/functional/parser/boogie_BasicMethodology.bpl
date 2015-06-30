// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo BasicMethodology

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

const BasicMethodology.ec: <ref>name;

const Component.y: <int>name;

const CS.f: <int>name;

const BasicMethodology.c: <ref>name;

const BasicMethodology.x: <int>name;

const System.IComparable`1...System.String: name;

const System.IEquatable`1...System.String: name;

const System.Boolean: name;

const System.Runtime.InteropServices._Exception: name;

const ExtensibleComponent: name;

const Component: name;

const C: name;

const BasicMethodology: name;

const System.Reflection.IReflect: name;

const System.Runtime.InteropServices._MemberInfo: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.Reflection.MemberInfo: name;

const Microsoft.Contracts.GuardException: name;

const SubClass: name;

const System.IConvertible: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Runtime.InteropServices._Type: name;

const CS: name;

const System.IComparable: name;

const System.Exception: name;

const System.Reflection.ICustomAttributeProvider: name;

const Microsoft.Contracts.ICheckedException: name;

const System.Collections.IEnumerable: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.ICloneable: name;

axiom !IsStaticField(BasicMethodology.x);

axiom IsDirectlyModifiableField(BasicMethodology.x);

axiom DeclType(BasicMethodology.x) == BasicMethodology;

axiom AsRangeField(BasicMethodology.x, System.Int32) == BasicMethodology.x;

axiom !IsStaticField(Component.y);

axiom IsDirectlyModifiableField(Component.y);

axiom DeclType(Component.y) == Component;

axiom AsRangeField(Component.y, System.Int32) == Component.y;

axiom !IsStaticField(BasicMethodology.c);

axiom IsDirectlyModifiableField(BasicMethodology.c);

axiom AsRepField(BasicMethodology.c, BasicMethodology) == BasicMethodology.c;

axiom DeclType(BasicMethodology.c) == BasicMethodology;

axiom AsNonNullRefField(BasicMethodology.c, Component) == BasicMethodology.c;

axiom !IsStaticField(BasicMethodology.ec);

axiom IsDirectlyModifiableField(BasicMethodology.ec);

axiom AsRepField(BasicMethodology.ec, BasicMethodology) == BasicMethodology.ec;

axiom DeclType(BasicMethodology.ec) == BasicMethodology;

axiom AsNonNullRefField(BasicMethodology.ec, ExtensibleComponent) == BasicMethodology.ec;

axiom !IsStaticField(CS.f);

axiom IsDirectlyModifiableField(CS.f);

axiom DeclType(CS.f) == CS;

axiom AsRangeField(CS.f, System.Int32) == CS.f;

axiom BasicMethodology <: BasicMethodology;

axiom $BaseClass(BasicMethodology) == System.Object;

axiom BasicMethodology <: $BaseClass(BasicMethodology) && AsDirectSubClass(BasicMethodology, $BaseClass(BasicMethodology)) == BasicMethodology;

axiom !$IsImmutable(BasicMethodology) && $AsMutable(BasicMethodology) == BasicMethodology;

axiom Component <: Component;

axiom $BaseClass(Component) == System.Object;

axiom Component <: $BaseClass(Component) && AsDirectSubClass(Component, $BaseClass(Component)) == Component;

axiom !$IsImmutable(Component) && $AsMutable(Component) == Component;

axiom (forall $U: name :: { $U <: Component } $U <: Component ==> $U == Component);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Component } IsHeap($h) && $h[$oi, $inv] <: Component && $h[$oi, $localinv] != System.Object ==> $h[$oi, Component.y] <= 80);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: BasicMethodology } IsHeap($h) && $h[$oi, $inv] <: BasicMethodology && $h[$oi, $localinv] != System.Object ==> 10 <= $h[$oi, BasicMethodology.x] && $h[$oi, BasicMethodology.x] <= $h[$h[$oi, BasicMethodology.c], Component.y]);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure BasicMethodology.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation BasicMethodology.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, stack1o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, BasicMethodology);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block6069;

  block6069:
    goto block6086;

  block6086:
    // ----- load constant 10  ----- BasicMethodology.ssc(5,13)
    stack0i := 10;
    // ----- load field  ----- BasicMethodology.ssc(5,19)
    assert this != null;
    stack1i := $Heap[this, BasicMethodology.x];
    // ----- binary operator  ----- BasicMethodology.ssc(5,13)
    // ----- branch
    goto true6086to6205, false6086to6103;

  true6086to6205:
    assume stack0i <= stack1i;
    goto block6205;

  false6086to6103:
    assume stack0i > stack1i;
    goto block6103;

  block6205:
    goto block6222;

  block6103:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true6103to6154, false6103to6120;

  true6103to6154:
    assume !stack0b;
    goto block6154;

  false6103to6120:
    assume stack0b;
    goto block6120;

  block6154:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block6409;

  block6120:
    assume false;
    // ----- new object  ----- BasicMethodology.ssc(5,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(5,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(5,3)
    stack0o := stack50000o;
    // ----- throw  ----- BasicMethodology.ssc(5,3)
    assert stack0o != null;
    assume false;
    return;

  block6222:
    goto block6239;

  block6409:
    goto block6426;

  block6239:
    // ----- load field  ----- BasicMethodology.ssc(8,13)
    assert this != null;
    stack0i := $Heap[this, BasicMethodology.x];
    // ----- load field  ----- BasicMethodology.ssc(8,18)
    assert this != null;
    stack1o := $Heap[this, BasicMethodology.c];
    // ----- load field  ----- BasicMethodology.ssc(8,18)
    assert stack1o != null;
    stack1i := $Heap[stack1o, Component.y];
    // ----- binary operator  ----- BasicMethodology.ssc(8,13)
    // ----- branch
    goto true6239to6358, false6239to6256;

  true6239to6358:
    assume stack0i <= stack1i;
    goto block6358;

  false6239to6256:
    assume stack0i > stack1i;
    goto block6256;

  block6358:
    goto block6375;

  block6256:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true6256to6307, false6256to6273;

  block6426:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

  true6256to6307:
    assume !stack0b;
    goto block6307;

  false6256to6273:
    assume stack0b;
    goto block6273;

  block6307:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block6409;

  block6273:
    assume false;
    // ----- new object  ----- BasicMethodology.ssc(8,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(8,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(8,3)
    stack0o := stack50000o;
    // ----- throw  ----- BasicMethodology.ssc(8,3)
    assert stack0o != null;
    assume false;
    return;

  block6375:
    goto block6392;

  block6392:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block6409;

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



procedure BasicMethodology.P(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == BasicMethodology && $Heap[this, $localinv] == $typeof(this);
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



implementation BasicMethodology.P(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local8976: ref where $Is(local8976, System.Exception), stack0i: int, stack1o: ref, stack1i: int, stack0b: bool, local9010: int where InRange(local9010, System.Int32), local8993: int where InRange(local8993, System.Int32), stack0o: ref;

  entry:
    assume $IsNotNull(this, BasicMethodology);
    assume $Heap[this, $allocated] == true;
    goto block7990;

  block7990:
    goto block8245;

  block8245:
    // ----- nop
    goto block8262;

  block8262:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(22,22)
    temp0 := this;
    // ----- classic unpack  ----- BasicMethodology.ssc(22,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == BasicMethodology && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local8976 := null;
    goto block8279;

  block8279:
    // ----- load field  ----- BasicMethodology.ssc(23,11)
    assert this != null;
    stack0i := $Heap[this, BasicMethodology.x];
    // ----- load field  ----- BasicMethodology.ssc(23,15)
    assert this != null;
    stack1o := $Heap[this, BasicMethodology.c];
    // ----- load field  ----- BasicMethodology.ssc(23,15)
    assert stack1o != null;
    stack1i := $Heap[stack1o, Component.y];
    // ----- binary operator  ----- BasicMethodology.ssc(23,11)
    // ----- branch  ----- BasicMethodology.ssc(23,7)
    goto true8279to8347, false8279to8296;

  true8279to8347:
    assume stack0i >= stack1i;
    goto block8347;

  false8279to8296:
    assume stack0i < stack1i;
    goto block8296;

  block8347:
    // ----- load constant 10  ----- BasicMethodology.ssc(25,18)
    stack0i := 10;
    // ----- load field  ----- BasicMethodology.ssc(25,23)
    assert this != null;
    stack1i := $Heap[this, BasicMethodology.x];
    // ----- binary operator  ----- BasicMethodology.ssc(25,18)
    // ----- branch  ----- BasicMethodology.ssc(25,14)
    goto true8347to8398, false8347to8364;

  block8296:
    // ----- load field  ----- BasicMethodology.ssc(24,9)
    assert this != null;
    local9010 := $Heap[this, BasicMethodology.x];
    // ----- load constant 1  ----- BasicMethodology.ssc(24,9)
    stack0i := 1;
    // ----- binary operator  ----- BasicMethodology.ssc(24,9)
    stack0i := local9010 + stack0i;
    // ----- store field  ----- BasicMethodology.ssc(24,9)
    assert this != null;
    assert !($Heap[this, $inv] <: BasicMethodology);
    $Heap[this, BasicMethodology.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- BasicMethodology.ssc(24,9)
    stack0i := local9010;
    goto block8313;

  true8347to8398:
    assume stack0i >= stack1i;
    goto block8398;

  false8347to8364:
    assume stack0i < stack1i;
    goto block8364;

  block8398:
    goto block8415;

  block8364:
    // ----- load field  ----- BasicMethodology.ssc(26,9)
    assert this != null;
    local8993 := $Heap[this, BasicMethodology.x];
    // ----- load constant 1  ----- BasicMethodology.ssc(26,9)
    stack0i := 1;
    // ----- binary operator  ----- BasicMethodology.ssc(26,9)
    stack0i := local8993 - stack0i;
    // ----- store field  ----- BasicMethodology.ssc(26,9)
    assert this != null;
    assert !($Heap[this, $inv] <: BasicMethodology);
    $Heap[this, BasicMethodology.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- BasicMethodology.ssc(26,9)
    stack0i := local8993;
    goto block8381;

  block8313:
    // ----- nop  ----- BasicMethodology.ssc(24,9)
    goto block8330;

  block8415:
    // ----- nop  ----- BasicMethodology.ssc(28,5)
    goto block8432;

  block8381:
    // ----- nop  ----- BasicMethodology.ssc(26,9)
    goto block8398;

  block8330:
    // ----- branch  ----- BasicMethodology.ssc(25,9)
    goto block8432;

  block8432:
    goto block8449;

  block8449:
    // ----- branch
    goto block8619;

  block8619:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true8619to8721, false8619to8636;

  true8619to8721:
    assume local8976 == stack0o;
    goto block8721;

  false8619to8636:
    assume local8976 != stack0o;
    goto block8636;

  block8721:
    goto block8738;

  block8636:
    // ----- is instance
    // ----- branch
    goto true8636to8721, false8636to8653;

  true8636to8721:
    assume $As(local8976, Microsoft.Contracts.ICheckedException) != null;
    goto block8721;

  false8636to8653:
    assume $As(local8976, Microsoft.Contracts.ICheckedException) == null;
    goto block8653;

  block8653:
    // ----- branch
    goto block8670;

  block8738:
    // ----- classic pack  ----- BasicMethodology.ssc(28,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 10 <= $Heap[temp0, BasicMethodology.x];
    assert $Heap[temp0, BasicMethodology.x] <= $Heap[$Heap[temp0, BasicMethodology.c], Component.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == BasicMethodology ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := BasicMethodology;
    assume IsHeap($Heap);
    goto block8670;

  block8670:
    goto block8687;

  block8687:
    goto block8704;

  block8704:
    // ----- nop
    // ----- branch
    goto block8568;

  block8568:
    goto block8585;

  block8585:
    goto block8602;

  block8602:
    // ----- return
    return;

}



axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure BasicMethodology.PeekBelow(this: ref);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == BasicMethodology && $Heap[this, $localinv] == $typeof(this);
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



implementation BasicMethodology.PeekBelow(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local11254: ref where $Is(local11254, System.Exception), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, BasicMethodology);
    assume $Heap[this, $allocated] == true;
    goto block10064;

  block10064:
    goto block10319;

  block10319:
    // ----- nop
    goto block10336;

  block10336:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(35,22)
    temp0 := this;
    // ----- classic unpack  ----- BasicMethodology.ssc(35,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == BasicMethodology && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local11254 := null;
    goto block10353;

  block10353:
    // ----- serialized AssertStatement  ----- BasicMethodology.ssc(36,7)
    assert ($Heap[$Heap[this, BasicMethodology.ec], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, BasicMethodology.ec], $ownerRef], $inv] <: $Heap[$Heap[this, BasicMethodology.ec], $ownerFrame]) || $Heap[$Heap[$Heap[this, BasicMethodology.ec], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, BasicMethodology.ec], $ownerFrame])) && $Heap[$Heap[this, BasicMethodology.ec], $inv] == $typeof($Heap[this, BasicMethodology.ec]) && $Heap[$Heap[this, BasicMethodology.ec], $localinv] == $typeof($Heap[this, BasicMethodology.ec]);
    goto block10506;

  block10506:
    // ----- nop
    goto block10523;

  block10523:
    // ----- serialized AssertStatement  ----- BasicMethodology.ssc(37,7)
    assert ($Heap[$Heap[this, BasicMethodology.c], $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$Heap[this, BasicMethodology.c], $ownerRef], $inv] <: $Heap[$Heap[this, BasicMethodology.c], $ownerFrame]) || $Heap[$Heap[$Heap[this, BasicMethodology.c], $ownerRef], $localinv] == $BaseClass($Heap[$Heap[this, BasicMethodology.c], $ownerFrame])) && $Heap[$Heap[this, BasicMethodology.c], $inv] == Component && $Heap[$Heap[this, BasicMethodology.c], $localinv] == $typeof($Heap[this, BasicMethodology.c]);
    goto block10676;

  block10676:
    // ----- nop
    goto block10693;

  block10693:
    // ----- branch
    goto block10863;

  block10863:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true10863to10965, false10863to10880;

  true10863to10965:
    assume local11254 == stack0o;
    goto block10965;

  false10863to10880:
    assume local11254 != stack0o;
    goto block10880;

  block10965:
    goto block10982;

  block10880:
    // ----- is instance
    // ----- branch
    goto true10880to10965, false10880to10897;

  true10880to10965:
    assume $As(local11254, Microsoft.Contracts.ICheckedException) != null;
    goto block10965;

  false10880to10897:
    assume $As(local11254, Microsoft.Contracts.ICheckedException) == null;
    goto block10897;

  block10897:
    // ----- branch
    goto block10914;

  block10982:
    // ----- classic pack  ----- BasicMethodology.ssc(38,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 10 <= $Heap[temp0, BasicMethodology.x];
    assert $Heap[temp0, BasicMethodology.x] <= $Heap[$Heap[temp0, BasicMethodology.c], Component.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == BasicMethodology ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := BasicMethodology;
    assume IsHeap($Heap);
    goto block10914;

  block10914:
    goto block10931;

  block10931:
    goto block10948;

  block10948:
    // ----- nop
    // ----- branch
    goto block10812;

  block10812:
    goto block10829;

  block10829:
    goto block10846;

  block10846:
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

axiom ExtensibleComponent <: ExtensibleComponent;

axiom $BaseClass(ExtensibleComponent) == System.Object;

axiom ExtensibleComponent <: $BaseClass(ExtensibleComponent) && AsDirectSubClass(ExtensibleComponent, $BaseClass(ExtensibleComponent)) == ExtensibleComponent;

axiom !$IsImmutable(ExtensibleComponent) && $AsMutable(ExtensibleComponent) == ExtensibleComponent;

procedure BasicMethodology..cctor();
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



implementation BasicMethodology..cctor()
{

  entry:
    goto block11815;

  block11815:
    goto block11934;

  block11934:
    // ----- nop
    goto block11951;

  block11951:
    goto block11968;

  block11968:
    // ----- return
    return;

}



axiom SubClass <: SubClass;

axiom $BaseClass(SubClass) == BasicMethodology;

axiom SubClass <: $BaseClass(SubClass) && AsDirectSubClass(SubClass, $BaseClass(SubClass)) == SubClass;

axiom !$IsImmutable(SubClass) && $AsMutable(SubClass) == SubClass;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: SubClass } IsHeap($h) && $h[$oi, $inv] <: SubClass && $h[$oi, $localinv] != BasicMethodology ==> 30 <= $h[$oi, BasicMethodology.x]);

procedure SubClass.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation SubClass.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, SubClass);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block12784;

  block12784:
    goto block12801;

  block12801:
    // ----- load constant 30  ----- BasicMethodology.ssc(43,13)
    stack0i := 30;
    // ----- load field  ----- BasicMethodology.ssc(43,19)
    assert this != null;
    stack1i := $Heap[this, BasicMethodology.x];
    // ----- binary operator  ----- BasicMethodology.ssc(43,13)
    // ----- branch
    goto true12801to12920, false12801to12818;

  true12801to12920:
    assume stack0i <= stack1i;
    goto block12920;

  false12801to12818:
    assume stack0i > stack1i;
    goto block12818;

  block12920:
    goto block12937;

  block12818:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true12818to12869, false12818to12835;

  true12818to12869:
    assume !stack0b;
    goto block12869;

  false12818to12835:
    assume stack0b;
    goto block12835;

  block12869:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block12971;

  block12835:
    assume false;
    // ----- new object  ----- BasicMethodology.ssc(43,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(43,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(43,3)
    stack0o := stack50000o;
    // ----- throw  ----- BasicMethodology.ssc(43,3)
    assert stack0o != null;
    assume false;
    return;

  block12937:
    goto block12954;

  block12971:
    goto block12988;

  block12954:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block12971;

  block12988:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



procedure SubClass..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == SubClass && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(SubClass <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SubClass..ctor(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local15504: ref where $Is(local15504, System.Exception), stack0i: int, stack1i: int, stack0b: bool, stack0o: ref, temp2: ref, temp3: exposeVersionType, local15538: ref where $Is(local15538, System.Exception), temp4: ref;

  entry:
    assume $IsNotNull(this, SubClass);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block14059;

  block14059:
    goto block14127;

  block14127:
    goto block14144;

  block14144:
    goto block14161;

  block14161:
    goto block14178;

  block14178:
    // ----- call  ----- BasicMethodology.ssc(48,5)
    assert this != null;
    call BasicMethodology..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block14297;

  block14297:
    goto block14314;

  block14314:
    // ----- nop
    goto block14331;

  block14331:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(49,22)
    temp0 := this;
    // ----- classic unpack  ----- BasicMethodology.ssc(49,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == BasicMethodology && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local15504 := null;
    goto block14348;

  block14348:
    // ----- load field  ----- BasicMethodology.ssc(50,7)
    assert this != null;
    stack0i := $Heap[this, BasicMethodology.x];
    // ----- load constant 20  ----- BasicMethodology.ssc(50,17)
    stack1i := 20;
    // ----- binary operator  ----- BasicMethodology.ssc(50,7)
    stack0i := stack0i + stack1i;
    // ----- store field  ----- BasicMethodology.ssc(50,7)
    assert this != null;
    assert !($Heap[this, $inv] <: BasicMethodology);
    $Heap[this, BasicMethodology.x] := stack0i;
    assume IsHeap($Heap);
    goto block14365;

  block14365:
    // ----- load constant 80  ----- BasicMethodology.ssc(51,11)
    stack0i := 80;
    // ----- load field  ----- BasicMethodology.ssc(51,16)
    assert this != null;
    stack1i := $Heap[this, BasicMethodology.x];
    // ----- binary operator  ----- BasicMethodology.ssc(51,11)
    // ----- branch  ----- BasicMethodology.ssc(51,7)
    goto true14365to14399, false14365to14382;

  true14365to14399:
    assume stack0i >= stack1i;
    goto block14399;

  false14365to14382:
    assume stack0i < stack1i;
    goto block14382;

  block14399:
    goto block14416;

  block14382:
    // ----- load constant 80  ----- BasicMethodology.ssc(52,11)
    stack0i := 80;
    // ----- store field  ----- BasicMethodology.ssc(52,2)
    assert this != null;
    assert !($Heap[this, $inv] <: BasicMethodology);
    $Heap[this, BasicMethodology.x] := stack0i;
    assume IsHeap($Heap);
    goto block14399;

  block14416:
    goto block14433;

  block14433:
    // ----- load field  ----- BasicMethodology.ssc(54,11)
    assert this != null;
    stack0o := $Heap[this, BasicMethodology.c];
    // ----- load field  ----- BasicMethodology.ssc(54,11)
    assert stack0o != null;
    stack0i := $Heap[stack0o, Component.y];
    // ----- load field  ----- BasicMethodology.ssc(54,22)
    assert this != null;
    stack1i := $Heap[this, BasicMethodology.x];
    // ----- binary operator  ----- BasicMethodology.ssc(54,11)
    // ----- branch  ----- BasicMethodology.ssc(54,7)
    goto true14433to14603, false14433to14450;

  true14433to14603:
    assume stack0i >= stack1i;
    goto block14603;

  false14433to14450:
    assume stack0i < stack1i;
    goto block14450;

  block14603:
    goto block14620;

  block14450:
    // ----- load field  ----- BasicMethodology.ssc(55,26)
    assert this != null;
    stack0o := $Heap[this, BasicMethodology.c];
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(55,26)
    temp2 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(55,26)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Component && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local15538 := null;
    goto block14467;

  block14467:
    // ----- load field  ----- BasicMethodology.ssc(56,11)
    assert this != null;
    stack0o := $Heap[this, BasicMethodology.c];
    // ----- load constant 80  ----- BasicMethodology.ssc(56,22)
    stack1i := 80;
    // ----- store field  ----- BasicMethodology.ssc(56,11)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: Component) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, Component.y] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block14807;

  block14620:
    goto block14637;

  block14807:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14807to14909, false14807to14824;

  true14807to14909:
    assume local15538 == stack0o;
    goto block14909;

  false14807to14824:
    assume local15538 != stack0o;
    goto block14824;

  block14909:
    goto block14926;

  block14824:
    // ----- is instance
    // ----- branch
    goto true14824to14909, false14824to14841;

  block14637:
    // ----- branch
    goto block15079;

  true14824to14909:
    assume $As(local15538, Microsoft.Contracts.ICheckedException) != null;
    goto block14909;

  false14824to14841:
    assume $As(local15538, Microsoft.Contracts.ICheckedException) == null;
    goto block14841;

  block14841:
    // ----- branch
    goto block14858;

  block15079:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true15079to15181, false15079to15096;

  true15079to15181:
    assume local15504 == stack0o;
    goto block15181;

  false15079to15096:
    assume local15504 != stack0o;
    goto block15096;

  block15181:
    goto block15198;

  block15096:
    // ----- is instance
    // ----- branch
    goto true15096to15181, false15096to15113;

  block14926:
    // ----- classic pack  ----- BasicMethodology.ssc(57,9)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Component.y] <= 80;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Component ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Component;
    assume IsHeap($Heap);
    goto block14858;

  true15096to15181:
    assume $As(local15504, Microsoft.Contracts.ICheckedException) != null;
    goto block15181;

  false15096to15113:
    assume $As(local15504, Microsoft.Contracts.ICheckedException) == null;
    goto block15113;

  block15113:
    // ----- branch
    goto block15130;

  block14858:
    goto block14875;

  block15198:
    // ----- classic pack  ----- BasicMethodology.ssc(59,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 10 <= $Heap[temp0, BasicMethodology.x];
    assert $Heap[temp0, BasicMethodology.x] <= $Heap[$Heap[temp0, BasicMethodology.c], Component.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == BasicMethodology ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := BasicMethodology;
    assume IsHeap($Heap);
    goto block15130;

  block14875:
    goto block14892;

  block15130:
    goto block15147;

  block14892:
    // ----- nop
    // ----- branch
    goto block14586;

  block15147:
    goto block15164;

  block14586:
    goto block14603;

  block15164:
    // ----- nop
    // ----- branch
    goto block14756;

  block14756:
    goto block14773;

  block14773:
    goto block14790;

  block14790:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(60,3)
    temp4 := this;
    // ----- classic pack  ----- BasicMethodology.ssc(60,3)
    assert temp4 != null;
    assert $Heap[temp4, $inv] == BasicMethodology && $Heap[temp4, $localinv] == $typeof(temp4);
    assert 30 <= $Heap[temp4, BasicMethodology.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp4 && $Heap[$p, $ownerFrame] == SubClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp4, $inv] := SubClass;
    assume IsHeap($Heap);
    // ----- return  ----- BasicMethodology.ssc(60,3)
    return;

}



procedure BasicMethodology..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == BasicMethodology && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(BasicMethodology <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure SubClass.P(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == SubClass && $Heap[this, $localinv] == $typeof(this);
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



implementation SubClass.P(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local18785: ref where $Is(local18785, System.Exception), stack0i: int, stack1i: int, stack0b: bool, temp2: ref, temp3: exposeVersionType, local18819: ref where $Is(local18819, System.Exception), stack0o: ref, temp4: ref, temp5: exposeVersionType, local18853: ref where $Is(local18853, System.Exception);

  entry:
    assume $IsNotNull(this, SubClass);
    assume $Heap[this, $allocated] == true;
    goto block16949;

  block16949:
    goto block17204;

  block17204:
    // ----- nop
    goto block17221;

  block17221:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(63,22)
    temp0 := this;
    // ----- classic unpack  ----- BasicMethodology.ssc(63,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == SubClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := BasicMethodology;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local18785 := null;
    goto block17238;

  block17238:
    // ----- call  ----- BasicMethodology.ssc(64,7)
    assert this != null;
    call BasicMethodology.P(this);
    goto block17255;

  block17255:
    // ----- load field  ----- BasicMethodology.ssc(65,11)
    assert this != null;
    stack0i := $Heap[this, BasicMethodology.x];
    // ----- load constant 30  ----- BasicMethodology.ssc(65,20)
    stack1i := 30;
    // ----- binary operator  ----- BasicMethodology.ssc(65,11)
    // ----- branch  ----- BasicMethodology.ssc(65,7)
    goto true17255to17595, false17255to17272;

  true17255to17595:
    assume stack0i >= stack1i;
    goto block17595;

  false17255to17272:
    assume stack0i < stack1i;
    goto block17272;

  block17595:
    goto block17612;

  block17272:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(66,26)
    temp2 := this;
    // ----- classic unpack  ----- BasicMethodology.ssc(66,26)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == BasicMethodology && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local18819 := null;
    goto block17289;

  block17612:
    goto block17629;

  block17289:
    // ----- load constant 32  ----- BasicMethodology.ssc(67,20)
    stack0i := 32;
    // ----- store field  ----- BasicMethodology.ssc(67,11)
    assert this != null;
    assert !($Heap[this, $inv] <: BasicMethodology);
    $Heap[this, BasicMethodology.x] := stack0i;
    assume IsHeap($Heap);
    goto block17306;

  block17629:
    // ----- branch
    goto block18343;

  block17306:
    // ----- load field  ----- BasicMethodology.ssc(68,28)
    assert this != null;
    stack0o := $Heap[this, BasicMethodology.c];
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(68,28)
    temp4 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(68,28)
    assert temp4 != null;
    assert ($Heap[temp4, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp4, $ownerRef], $inv] <: $Heap[temp4, $ownerFrame]) || $Heap[$Heap[temp4, $ownerRef], $localinv] == $BaseClass($Heap[temp4, $ownerFrame])) && $Heap[temp4, $inv] == Component && $Heap[temp4, $localinv] == $typeof(temp4);
    $Heap[temp4, $inv] := System.Object;
    havoc temp5;
    $Heap[temp4, $exposeVersion] := temp5;
    assume IsHeap($Heap);
    local18853 := null;
    goto block17323;

  block18343:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true18343to18445, false18343to18360;

  true18343to18445:
    assume local18785 == stack0o;
    goto block18445;

  false18343to18360:
    assume local18785 != stack0o;
    goto block18360;

  block18445:
    goto block18462;

  block18360:
    // ----- is instance
    // ----- branch
    goto true18360to18445, false18360to18377;

  block17323:
    // ----- load field  ----- BasicMethodology.ssc(69,13)
    assert this != null;
    stack0o := $Heap[this, BasicMethodology.c];
    // ----- load constant 32  ----- BasicMethodology.ssc(69,24)
    stack1i := 32;
    // ----- store field  ----- BasicMethodology.ssc(69,13)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: Component) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, Component.y] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block17799;

  true18360to18445:
    assume $As(local18785, Microsoft.Contracts.ICheckedException) != null;
    goto block18445;

  false18360to18377:
    assume $As(local18785, Microsoft.Contracts.ICheckedException) == null;
    goto block18377;

  block18377:
    // ----- branch
    goto block18394;

  block17799:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true17799to17901, false17799to17816;

  true17799to17901:
    assume local18853 == stack0o;
    goto block17901;

  false17799to17816:
    assume local18853 != stack0o;
    goto block17816;

  block17901:
    goto block17918;

  block17816:
    // ----- is instance
    // ----- branch
    goto true17816to17901, false17816to17833;

  block18462:
    // ----- classic pack  ----- BasicMethodology.ssc(73,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == BasicMethodology && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 30 <= $Heap[temp0, BasicMethodology.x];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == SubClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := SubClass;
    assume IsHeap($Heap);
    goto block18394;

  true17816to17901:
    assume $As(local18853, Microsoft.Contracts.ICheckedException) != null;
    goto block17901;

  false17816to17833:
    assume $As(local18853, Microsoft.Contracts.ICheckedException) == null;
    goto block17833;

  block17833:
    // ----- branch
    goto block17850;

  block18394:
    goto block18411;

  block17918:
    // ----- classic pack  ----- BasicMethodology.ssc(70,11)
    assert temp4 != null;
    assert $Heap[temp4, $inv] == System.Object && $Heap[temp4, $localinv] == $typeof(temp4);
    assert $Heap[temp4, Component.y] <= 80;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp4 && $Heap[$p, $ownerFrame] == Component ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp4, $inv] := Component;
    assume IsHeap($Heap);
    goto block17850;

  block18411:
    goto block18428;

  block17850:
    goto block17867;

  block18428:
    // ----- nop
    // ----- branch
    goto block17748;

  block17867:
    goto block17884;

  block17748:
    goto block17765;

  block17884:
    // ----- nop
    // ----- branch
    goto block17442;

  block17765:
    goto block17782;

  block17442:
    goto block17459;

  block17782:
    // ----- return
    return;

  block17459:
    // ----- branch
    goto block18071;

  block18071:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true18071to18173, false18071to18088;

  true18071to18173:
    assume local18819 == stack0o;
    goto block18173;

  false18071to18088:
    assume local18819 != stack0o;
    goto block18088;

  block18173:
    goto block18190;

  block18088:
    // ----- is instance
    // ----- branch
    goto true18088to18173, false18088to18105;

  true18088to18173:
    assume $As(local18819, Microsoft.Contracts.ICheckedException) != null;
    goto block18173;

  false18088to18105:
    assume $As(local18819, Microsoft.Contracts.ICheckedException) == null;
    goto block18105;

  block18105:
    // ----- branch
    goto block18122;

  block18190:
    // ----- classic pack  ----- BasicMethodology.ssc(71,9)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert 10 <= $Heap[temp2, BasicMethodology.x];
    assert $Heap[temp2, BasicMethodology.x] <= $Heap[$Heap[temp2, BasicMethodology.c], Component.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == BasicMethodology ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := BasicMethodology;
    assume IsHeap($Heap);
    goto block18122;

  block18122:
    goto block18139;

  block18139:
    goto block18156;

  block18156:
    // ----- nop
    // ----- branch
    goto block17578;

  block17578:
    goto block17595;

}



procedure SubClass..cctor();
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



implementation SubClass..cctor()
{

  entry:
    goto block19414;

  block19414:
    goto block19533;

  block19533:
    // ----- nop
    goto block19550;

  block19550:
    goto block19567;

  block19567:
    // ----- return
    return;

}



procedure Component.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Component.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Component);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block20383;

  block20383:
    goto block20400;

  block20400:
    // ----- load field  ----- BasicMethodology.ssc(79,13)
    assert this != null;
    stack0i := $Heap[this, Component.y];
    // ----- load constant 80  ----- BasicMethodology.ssc(79,18)
    stack1i := 80;
    // ----- binary operator  ----- BasicMethodology.ssc(79,13)
    // ----- branch
    goto true20400to20519, false20400to20417;

  true20400to20519:
    assume stack0i <= stack1i;
    goto block20519;

  false20400to20417:
    assume stack0i > stack1i;
    goto block20417;

  block20519:
    goto block20536;

  block20417:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true20417to20468, false20417to20434;

  true20417to20468:
    assume !stack0b;
    goto block20468;

  false20417to20434:
    assume stack0b;
    goto block20434;

  block20468:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block20570;

  block20434:
    assume false;
    // ----- new object  ----- BasicMethodology.ssc(79,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(79,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(79,3)
    stack0o := stack50000o;
    // ----- throw  ----- BasicMethodology.ssc(79,3)
    assert stack0o != null;
    assume false;
    return;

  block20536:
    goto block20553;

  block20570:
    goto block20587;

  block20553:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block20570;

  block20587:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



procedure Component..ctor$System.Int32(this: ref, z$in: int where InRange(z$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires z$in <= 80;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, Component.y] == z$in;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Component && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Component <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Component..ctor$System.Int32(this: ref, z$in: int)
{
  var z: int where InRange(z, System.Int32), temp0: ref;

  entry:
    assume $IsNotNull(this, Component);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    z := z$in;
    assume $Heap[this, Component.y] == 0;
    goto block21403;

  block21403:
    goto block21607;

  block21607:
    // ----- nop
    goto block21624;

  block21624:
    goto block21641;

  block21641:
    goto block21658;

  block21658:
    // ----- call  ----- BasicMethodology.ssc(82,5)
    assert this != null;
    call System.Object..ctor(this);
    goto block21777;

  block21777:
    goto block21794;

  block21794:
    // ----- nop
    goto block21811;

  block21811:
    // ----- store field  ----- BasicMethodology.ssc(85,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Component) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Component.y] := z;
    assume IsHeap($Heap);
    goto block21828;

  block21828:
    goto block21845;

  block21845:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(86,3)
    temp0 := this;
    // ----- classic pack  ----- BasicMethodology.ssc(86,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Component.y] <= 80;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Component ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Component;
    assume IsHeap($Heap);
    goto block22049;

  block22049:
    // ----- nop
    goto block22066;

  block22066:
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



procedure Component..ctor$System.Int32$System.Boolean(this: ref, z$in: int where InRange(z$in, System.Int32), bad$in: bool where true);
  free requires true;
  free requires true;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Component && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Component <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Component..ctor$System.Int32$System.Boolean(this: ref, z$in: int, bad$in: bool)
{
  var z: int where InRange(z, System.Int32), bad: bool where true, stack0b: bool, stack0i: int, temp0: ref;

  entry:
    assume $IsNotNull(this, Component);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    z := z$in;
    bad := bad$in;
    assume $Heap[this, Component.y] == 0;
    goto block22542;

  block22542:
    goto block22559;

  block22559:
    goto block22576;

  block22576:
    goto block22593;

  block22593:
    // ----- call  ----- BasicMethodology.ssc(89,3)
    assert this != null;
    call System.Object..ctor(this);
    goto block22712;

  block22712:
    goto block22729;

  block22729:
    // ----- nop
    goto block22746;

  block22746:
    // ----- copy  ----- BasicMethodology.ssc(90,14)
    stack0b := bad;
    // ----- unary operator  ----- BasicMethodology.ssc(90,14)
    // ----- branch  ----- BasicMethodology.ssc(90,5)
    goto true22746to22780, false22746to22763;

  true22746to22780:
    assume !stack0b;
    goto block22780;

  false22746to22763:
    assume stack0b;
    goto block22763;

  block22780:
    goto block22797;

  block22763:
    // ----- copy  ----- BasicMethodology.ssc(90,5)
    stack0i := z;
    // ----- branch  ----- BasicMethodology.ssc(90,5)
    goto block22814;

  block22797:
    // ----- load constant 0  ----- BasicMethodology.ssc(90,5)
    stack0i := 0;
    goto block22814;

  block22814:
    goto block22831;

  block22831:
    // ----- store field  ----- BasicMethodology.ssc(90,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Component) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Component.y] := stack0i;
    assume IsHeap($Heap);
    goto block22848;

  block22848:
    goto block22865;

  block22865:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(91,3)
    temp0 := this;
    // ----- classic pack  ----- BasicMethodology.ssc(91,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Component.y] <= 80;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Component ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Component;
    assume IsHeap($Heap);
    // ----- return  ----- BasicMethodology.ssc(91,3)
    return;

}



procedure Component..cctor();
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



implementation Component..cctor()
{

  entry:
    goto block23460;

  block23460:
    goto block23579;

  block23579:
    // ----- nop
    goto block23596;

  block23596:
    goto block23613;

  block23613:
    // ----- return
    return;

}



procedure ExtensibleComponent..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == ExtensibleComponent && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(ExtensibleComponent <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ExtensibleComponent..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, ExtensibleComponent);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block24259;

  block24259:
    goto block24276;

  block24276:
    goto block24293;

  block24293:
    // ----- call  ----- BasicMethodology.ssc(94,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block24310;

  block24310:
    goto block24327;

  block24327:
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == ExtensibleComponent ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := ExtensibleComponent;
    assume IsHeap($Heap);
    return;

}



axiom C <: C;

axiom $BaseClass(C) == System.Object;

axiom C <: $BaseClass(C) && AsDirectSubClass(C, $BaseClass(C)) == C;

axiom !$IsImmutable(C) && $AsMutable(C) == C;

axiom CS <: CS;

axiom $BaseClass(CS) == C;

axiom CS <: $BaseClass(CS) && AsDirectSubClass(CS, $BaseClass(CS)) == CS;

axiom !$IsImmutable(CS) && $AsMutable(CS) == CS;

axiom (forall $U: name :: { $U <: CS } $U <: CS ==> $U == CS);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: CS } IsHeap($h) && $h[$oi, $inv] <: CS && $h[$oi, $localinv] != C ==> $h[$oi, CS.f] != 0);

axiom (forall $U: name :: { $U <: C } $U <: C ==> $U == C || $U <: CS);

procedure C.foo(this: ref) returns ($result: int where InRange($result, System.Int32));
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == C && $Heap[this, $localinv] == $typeof(this);
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



implementation C.foo(this: ref) returns ($result: int)
{
  var return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    goto block24480;

  block24480:
    goto block24497;

  block24497:
    // ----- load constant 5  ----- BasicMethodology.ssc(102,5)
    return.value := 5;
    // ----- branch
    goto block24514;

  block24514:
    goto block24531;

  block24531:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- BasicMethodology.ssc(103,3)
    stack0i := return.value;
    // ----- return  ----- BasicMethodology.ssc(103,3)
    $result := stack0i;
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

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block24701;

  block24701:
    goto block24718;

  block24718:
    goto block24735;

  block24735:
    // ----- call  ----- BasicMethodology.ssc(100,7)
    assert this != null;
    call System.Object..ctor(this);
    goto block24752;

  block24752:
    goto block24769;

  block24769:
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := C;
    assume IsHeap($Heap);
    return;

}



procedure CS.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation CS.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, stack50000o: ref, stack0o: ref, return.value: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, CS);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block25075;

  block25075:
    goto block25092;

  block25092:
    // ----- load field  ----- BasicMethodology.ssc(108,13)
    assert this != null;
    stack0i := $Heap[this, CS.f];
    // ----- load constant 0  ----- BasicMethodology.ssc(108,18)
    stack1i := 0;
    // ----- binary operator  ----- BasicMethodology.ssc(108,13)
    // ----- branch
    goto true25092to25211, false25092to25109;

  true25092to25211:
    assume stack0i != stack1i;
    goto block25211;

  false25092to25109:
    assume stack0i == stack1i;
    goto block25109;

  block25211:
    goto block25228;

  block25109:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true25109to25160, false25109to25126;

  true25109to25160:
    assume !stack0b;
    goto block25160;

  false25109to25126:
    assume stack0b;
    goto block25126;

  block25160:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block25262;

  block25126:
    assume false;
    // ----- new object  ----- BasicMethodology.ssc(108,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(108,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(108,3)
    stack0o := stack50000o;
    // ----- throw  ----- BasicMethodology.ssc(108,3)
    assert stack0o != null;
    assume false;
    return;

  block25228:
    goto block25245;

  block25245:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block25262;

  block25262:
    goto block25279;

  block25279:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
    // ----- return
    $result := stack0b;
    return;

}



procedure CS.foo(this: ref) returns ($result: int where InRange($result, System.Int32));
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == CS && $Heap[this, $localinv] == $typeof(this);
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



implementation CS.foo(this: ref) returns ($result: int)
{
  var stack0i: int, stack1i: int, return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32);

  entry:
    assume $IsNotNull(this, CS);
    assume $Heap[this, $allocated] == true;
    goto block25721;

  block25721:
    goto block25925;

  block25925:
    // ----- nop
    goto block25942;

  block25942:
    // ----- load constant 5  ----- BasicMethodology.ssc(111,12)
    stack0i := 5;
    // ----- load field  ----- BasicMethodology.ssc(111,16)
    assert this != null;
    stack1i := $Heap[this, CS.f];
    // ----- binary operator  ----- BasicMethodology.ssc(111,12)
    assert stack1i != 0;
    stack0i := stack0i / stack1i;
    // ----- copy  ----- BasicMethodology.ssc(111,5)
    return.value := stack0i;
    // ----- branch
    goto block25959;

  block25959:
    goto block25976;

  block25976:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

}



procedure CS..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == CS && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(CS <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation CS..ctor(this: ref)
{
  var stack0i: int, temp0: ref;

  entry:
    assume $IsNotNull(this, CS);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, CS.f] == 0;
    goto block26350;

  block26350:
    goto block26367;

  block26367:
    goto block26384;

  block26384:
    goto block26401;

  block26401:
    goto block26418;

  block26418:
    // ----- load constant 1  ----- BasicMethodology.ssc(115,9)
    stack0i := 1;
    // ----- store field  ----- BasicMethodology.ssc(115,5)
    assert this != null;
    assert !($Heap[this, $inv] <: CS) || $Heap[this, $localinv] == C;
    $Heap[this, CS.f] := stack0i;
    assume IsHeap($Heap);
    goto block26435;

  block26435:
    // ----- call  ----- BasicMethodology.ssc(116,5)
    assert this != null;
    call C..ctor(this);
    goto block26554;

  block26554:
    goto block26571;

  block26571:
    // ----- nop
    goto block26588;

  block26588:
    goto block26605;

  block26605:
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(117,3)
    temp0 := this;
    // ----- classic pack  ----- BasicMethodology.ssc(117,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := CS;
    assume IsHeap($Heap);
    // ----- return  ----- BasicMethodology.ssc(117,3)
    return;

}



procedure CS.test0();
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



implementation CS.test0()
{
  var stack50000o: ref, stack0o: ref, t: ref where $Is(t, C);

  entry:
    goto block26979;

  block26979:
    goto block26996;

  block26996:
    // ----- new object  ----- BasicMethodology.ssc(120,11)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == CS;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(120,11)
    assert stack50000o != null;
    call CS..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(120,5)
    stack0o := stack50000o;
    // ----- copy  ----- BasicMethodology.ssc(120,5)
    t := stack0o;
    goto block27013;

  block27013:
    // ----- serialized AssertStatement  ----- BasicMethodology.ssc(121,5)
    assert ($Heap[t, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t, $ownerRef], $inv] <: $Heap[t, $ownerFrame]) || $Heap[$Heap[t, $ownerRef], $localinv] == $BaseClass($Heap[t, $ownerFrame])) && $Heap[t, $inv] == C && $Heap[t, $localinv] == $typeof(t);
    goto block27166;

  block27166:
    // ----- nop
    goto block27183;

  block27183:
    goto block27200;

  block27200:
    // ----- return  ----- BasicMethodology.ssc(122,3)
    return;

}



procedure CS.test1();
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



implementation CS.test1()
{
  var stack50000o: ref, stack0o: ref, t: ref where $Is(t, C), temp0: ref, temp1: exposeVersionType, local28543: ref where $Is(local28543, System.Exception), local28560: ref where $Is(local28560, C), stack1s: struct, stack1o: ref, temp2: exposeVersionType, stack1i: int, stack0i: int, stack0b: bool;

  entry:
    goto block27812;

  block27812:
    goto block27880;

  block27880:
    // ----- new object  ----- BasicMethodology.ssc(125,11)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == CS;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(125,11)
    assert stack50000o != null;
    call CS..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(125,5)
    stack0o := stack50000o;
    // ----- copy  ----- BasicMethodology.ssc(125,5)
    t := stack0o;
    goto block27897;

  block27897:
    // ----- castclass  ----- BasicMethodology.ssc(126,22)
    assert $Is(t, CS);
    stack0o := t;
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(126,22)
    temp0 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(126,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == CS && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := C;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local28543 := null;
    goto block27914;

  block27914:
    // ----- copy  ----- BasicMethodology.ssc(127,24)
    local28560 := t;
    // ----- copy  ----- BasicMethodology.ssc(127,24)
    stack0o := local28560;
    // ----- load token  ----- BasicMethodology.ssc(127,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(127,24)
    stack1o := TypeObject(C);
    // ----- classic unpack  ----- BasicMethodology.ssc(127,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == C && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp2;
    $Heap[stack0o, $exposeVersion] := temp2;
    assume IsHeap($Heap);
    goto block27931;

  block27931:
    // ----- castclass  ----- BasicMethodology.ssc(128,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant 0  ----- BasicMethodology.ssc(128,21)
    stack1i := 0;
    // ----- store field  ----- BasicMethodology.ssc(128,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- call  ----- BasicMethodology.ssc(129,9)
    assert t != null;
    call stack0i := C.foo$.Virtual.$(t);
    // ----- castclass  ----- BasicMethodology.ssc(130,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant 1  ----- BasicMethodology.ssc(130,21)
    stack1i := 1;
    // ----- store field  ----- BasicMethodology.ssc(130,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block28169;

  block28169:
    // ----- copy  ----- BasicMethodology.ssc(131,7)
    stack0o := local28560;
    // ----- load token  ----- BasicMethodology.ssc(131,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(131,7)
    stack1o := TypeObject(C);
    // ----- classic pack  ----- BasicMethodology.ssc(131,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := C;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block27982;

  block27982:
    goto block27999;

  block27999:
    // ----- branch
    goto block28186;

  block28186:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true28186to28288, false28186to28203;

  true28186to28288:
    assume local28543 == stack0o;
    goto block28288;

  false28186to28203:
    assume local28543 != stack0o;
    goto block28203;

  block28288:
    goto block28305;

  block28203:
    // ----- is instance
    // ----- branch
    goto true28203to28288, false28203to28220;

  true28203to28288:
    assume $As(local28543, Microsoft.Contracts.ICheckedException) != null;
    goto block28288;

  false28203to28220:
    assume $As(local28543, Microsoft.Contracts.ICheckedException) == null;
    goto block28220;

  block28220:
    // ----- branch
    goto block28237;

  block28305:
    // ----- classic pack  ----- BasicMethodology.ssc(132,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := CS;
    assume IsHeap($Heap);
    goto block28237;

  block28237:
    goto block28254;

  block28254:
    goto block28271;

  block28271:
    // ----- nop
    // ----- branch
    goto block28118;

  block28118:
    goto block28135;

  block28135:
    goto block28152;

  block28152:
    // ----- return  ----- BasicMethodology.ssc(133,3)
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

procedure C.foo$.Virtual.$(this: ref) returns ($result: int where InRange($result, System.Int32));
  // target object is consistent
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this);
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



procedure CS.test2();
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



implementation CS.test2()
{
  var stack50000o: ref, stack0o: ref, t: ref where $Is(t, C), temp0: ref, temp1: exposeVersionType, local30821: ref where $Is(local30821, System.Exception), local30838: ref where $Is(local30838, C), stack1s: struct, stack1o: ref, temp2: exposeVersionType, stack1i: int, stack0b: bool, stack0i: int, temp3: ref, temp4: exposeVersionType, local30923: ref where $Is(local30923, System.Exception), local30940: ref where $Is(local30940, C), temp5: exposeVersionType;

  entry:
    goto block29495;

  block29495:
    goto block29563;

  block29563:
    // ----- new object  ----- BasicMethodology.ssc(136,11)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == CS;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(136,11)
    assert stack50000o != null;
    call CS..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(136,5)
    stack0o := stack50000o;
    // ----- copy  ----- BasicMethodology.ssc(136,5)
    t := stack0o;
    goto block29580;

  block29580:
    // ----- castclass  ----- BasicMethodology.ssc(137,22)
    assert $Is(t, CS);
    stack0o := t;
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(137,22)
    temp0 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(137,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == CS && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := C;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local30821 := null;
    goto block29597;

  block29597:
    // ----- copy  ----- BasicMethodology.ssc(138,24)
    local30838 := t;
    // ----- copy  ----- BasicMethodology.ssc(138,24)
    stack0o := local30838;
    // ----- load token  ----- BasicMethodology.ssc(138,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(138,24)
    stack1o := TypeObject(C);
    // ----- classic unpack  ----- BasicMethodology.ssc(138,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == C && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp2;
    $Heap[stack0o, $exposeVersion] := temp2;
    assume IsHeap($Heap);
    goto block29614;

  block29614:
    // ----- castclass  ----- BasicMethodology.ssc(139,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant 0  ----- BasicMethodology.ssc(139,21)
    stack1i := 0;
    // ----- store field  ----- BasicMethodology.ssc(139,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block30107;

  block30107:
    // ----- copy  ----- BasicMethodology.ssc(140,7)
    stack0o := local30838;
    // ----- load token  ----- BasicMethodology.ssc(140,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(140,7)
    stack1o := TypeObject(C);
    // ----- classic pack  ----- BasicMethodology.ssc(140,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := C;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block29665;

  block29665:
    goto block29682;

  block29682:
    // ----- branch
    goto block30124;

  block30124:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true30124to30226, false30124to30141;

  true30124to30226:
    assume local30821 == stack0o;
    goto block30226;

  false30124to30141:
    assume local30821 != stack0o;
    goto block30141;

  block30226:
    goto block30243;

  block30141:
    // ----- is instance
    // ----- branch
    goto true30141to30226, false30141to30158;

  true30141to30226:
    assume $As(local30821, Microsoft.Contracts.ICheckedException) != null;
    goto block30226;

  false30141to30158:
    assume $As(local30821, Microsoft.Contracts.ICheckedException) == null;
    goto block30158;

  block30158:
    // ----- branch
    goto block30175;

  block30243:
    // ----- classic pack  ----- BasicMethodology.ssc(141,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := CS;
    assume IsHeap($Heap);
    goto block30175;

  block30175:
    goto block30192;

  block30192:
    goto block30209;

  block30209:
    // ----- nop
    // ----- branch
    goto block29801;

  block29801:
    goto block29818;

  block29818:
    // ----- call  ----- BasicMethodology.ssc(142,5)
    assert t != null;
    call stack0i := C.foo$.Virtual.$(t);
    goto block29835;

  block29835:
    // ----- castclass  ----- BasicMethodology.ssc(143,22)
    assert $Is(t, CS);
    stack0o := t;
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(143,22)
    temp3 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(143,22)
    assert temp3 != null;
    assert ($Heap[temp3, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp3, $ownerRef], $inv] <: $Heap[temp3, $ownerFrame]) || $Heap[$Heap[temp3, $ownerRef], $localinv] == $BaseClass($Heap[temp3, $ownerFrame])) && $Heap[temp3, $inv] == CS && $Heap[temp3, $localinv] == $typeof(temp3);
    $Heap[temp3, $inv] := C;
    havoc temp4;
    $Heap[temp3, $exposeVersion] := temp4;
    assume IsHeap($Heap);
    local30923 := null;
    goto block29852;

  block29852:
    // ----- copy  ----- BasicMethodology.ssc(144,24)
    local30940 := t;
    // ----- copy  ----- BasicMethodology.ssc(144,24)
    stack0o := local30940;
    // ----- load token  ----- BasicMethodology.ssc(144,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(144,24)
    stack1o := TypeObject(C);
    // ----- classic unpack  ----- BasicMethodology.ssc(144,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == C && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp5;
    $Heap[stack0o, $exposeVersion] := temp5;
    assume IsHeap($Heap);
    goto block29869;

  block29869:
    // ----- castclass  ----- BasicMethodology.ssc(145,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant 1  ----- BasicMethodology.ssc(145,21)
    stack1i := 1;
    // ----- store field  ----- BasicMethodology.ssc(145,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block30396;

  block30396:
    // ----- copy  ----- BasicMethodology.ssc(146,7)
    stack0o := local30940;
    // ----- load token  ----- BasicMethodology.ssc(146,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(146,7)
    stack1o := TypeObject(C);
    // ----- classic pack  ----- BasicMethodology.ssc(146,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := C;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block29920;

  block29920:
    goto block29937;

  block29937:
    // ----- branch
    goto block30413;

  block30413:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true30413to30515, false30413to30430;

  true30413to30515:
    assume local30923 == stack0o;
    goto block30515;

  false30413to30430:
    assume local30923 != stack0o;
    goto block30430;

  block30515:
    goto block30532;

  block30430:
    // ----- is instance
    // ----- branch
    goto true30430to30515, false30430to30447;

  true30430to30515:
    assume $As(local30923, Microsoft.Contracts.ICheckedException) != null;
    goto block30515;

  false30430to30447:
    assume $As(local30923, Microsoft.Contracts.ICheckedException) == null;
    goto block30447;

  block30447:
    // ----- branch
    goto block30464;

  block30532:
    // ----- classic pack  ----- BasicMethodology.ssc(147,5)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == C && $Heap[temp3, $localinv] == $typeof(temp3);
    assert $Heap[temp3, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := CS;
    assume IsHeap($Heap);
    goto block30464;

  block30464:
    goto block30481;

  block30481:
    goto block30498;

  block30498:
    // ----- nop
    // ----- branch
    goto block30056;

  block30056:
    goto block30073;

  block30073:
    goto block30090;

  block30090:
    // ----- return  ----- BasicMethodology.ssc(148,3)
    return;

}



procedure CS.test3();
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



implementation CS.test3()
{
  var stack50000o: ref, stack0o: ref, t: ref where $Is(t, C), temp0: ref, temp1: exposeVersionType, local33184: ref where $Is(local33184, System.Exception), local33201: ref where $Is(local33201, C), stack1s: struct, stack1o: ref, temp2: exposeVersionType, stack1i: int, stack0b: bool, stack0i: int, temp3: ref, temp4: exposeVersionType, local33286: ref where $Is(local33286, System.Exception), local33303: ref where $Is(local33303, C), temp5: exposeVersionType;

  entry:
    goto block31858;

  block31858:
    goto block31926;

  block31926:
    // ----- new object  ----- BasicMethodology.ssc(151,11)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == CS;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- BasicMethodology.ssc(151,11)
    assert stack50000o != null;
    call CS..ctor(stack50000o);
    // ----- copy  ----- BasicMethodology.ssc(151,5)
    stack0o := stack50000o;
    // ----- copy  ----- BasicMethodology.ssc(151,5)
    t := stack0o;
    goto block31943;

  block31943:
    // ----- castclass  ----- BasicMethodology.ssc(152,22)
    assert $Is(t, CS);
    stack0o := t;
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(152,22)
    temp0 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(152,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == CS && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := C;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local33184 := null;
    goto block31960;

  block31960:
    // ----- copy  ----- BasicMethodology.ssc(153,24)
    local33201 := t;
    // ----- copy  ----- BasicMethodology.ssc(153,24)
    stack0o := local33201;
    // ----- load token  ----- BasicMethodology.ssc(153,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(153,24)
    stack1o := TypeObject(C);
    // ----- classic unpack  ----- BasicMethodology.ssc(153,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == C && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp2;
    $Heap[stack0o, $exposeVersion] := temp2;
    assume IsHeap($Heap);
    goto block31977;

  block31977:
    // ----- castclass  ----- BasicMethodology.ssc(154,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant -1  ----- BasicMethodology.ssc(154,21)
    stack1i := -1;
    // ----- store field  ----- BasicMethodology.ssc(154,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block32470;

  block32470:
    // ----- copy  ----- BasicMethodology.ssc(155,7)
    stack0o := local33201;
    // ----- load token  ----- BasicMethodology.ssc(155,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(155,7)
    stack1o := TypeObject(C);
    // ----- classic pack  ----- BasicMethodology.ssc(155,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := C;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block32028;

  block32028:
    goto block32045;

  block32045:
    // ----- branch
    goto block32487;

  block32487:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true32487to32589, false32487to32504;

  true32487to32589:
    assume local33184 == stack0o;
    goto block32589;

  false32487to32504:
    assume local33184 != stack0o;
    goto block32504;

  block32589:
    goto block32606;

  block32504:
    // ----- is instance
    // ----- branch
    goto true32504to32589, false32504to32521;

  true32504to32589:
    assume $As(local33184, Microsoft.Contracts.ICheckedException) != null;
    goto block32589;

  false32504to32521:
    assume $As(local33184, Microsoft.Contracts.ICheckedException) == null;
    goto block32521;

  block32521:
    // ----- branch
    goto block32538;

  block32606:
    // ----- classic pack  ----- BasicMethodology.ssc(156,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == C && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := CS;
    assume IsHeap($Heap);
    goto block32538;

  block32538:
    goto block32555;

  block32555:
    goto block32572;

  block32572:
    // ----- nop
    // ----- branch
    goto block32164;

  block32164:
    goto block32181;

  block32181:
    // ----- call  ----- BasicMethodology.ssc(157,5)
    assert t != null;
    call stack0i := C.foo$.Virtual.$(t);
    goto block32198;

  block32198:
    // ----- castclass  ----- BasicMethodology.ssc(158,22)
    assert $Is(t, CS);
    stack0o := t;
    // ----- FrameGuard processing  ----- BasicMethodology.ssc(158,22)
    temp3 := stack0o;
    // ----- classic unpack  ----- BasicMethodology.ssc(158,22)
    assert temp3 != null;
    assert ($Heap[temp3, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp3, $ownerRef], $inv] <: $Heap[temp3, $ownerFrame]) || $Heap[$Heap[temp3, $ownerRef], $localinv] == $BaseClass($Heap[temp3, $ownerFrame])) && $Heap[temp3, $inv] == CS && $Heap[temp3, $localinv] == $typeof(temp3);
    $Heap[temp3, $inv] := C;
    havoc temp4;
    $Heap[temp3, $exposeVersion] := temp4;
    assume IsHeap($Heap);
    local33286 := null;
    goto block32215;

  block32215:
    // ----- copy  ----- BasicMethodology.ssc(159,24)
    local33303 := t;
    // ----- copy  ----- BasicMethodology.ssc(159,24)
    stack0o := local33303;
    // ----- load token  ----- BasicMethodology.ssc(159,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(159,24)
    stack1o := TypeObject(C);
    // ----- classic unpack  ----- BasicMethodology.ssc(159,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == C && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp5;
    $Heap[stack0o, $exposeVersion] := temp5;
    assume IsHeap($Heap);
    goto block32232;

  block32232:
    // ----- castclass  ----- BasicMethodology.ssc(160,10)
    assert $Is(t, CS);
    stack0o := t;
    // ----- load constant 1  ----- BasicMethodology.ssc(160,21)
    stack1i := 1;
    // ----- store field  ----- BasicMethodology.ssc(160,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: CS) || $Heap[stack0o, $localinv] == C;
    $Heap[stack0o, CS.f] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block32759;

  block32759:
    // ----- copy  ----- BasicMethodology.ssc(161,7)
    stack0o := local33303;
    // ----- load token  ----- BasicMethodology.ssc(161,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, C);
    // ----- statically resolved GetTypeFromHandle call  ----- BasicMethodology.ssc(161,7)
    stack1o := TypeObject(C);
    // ----- classic pack  ----- BasicMethodology.ssc(161,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := C;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block32283;

  block32283:
    goto block32300;

  block32300:
    // ----- branch
    goto block32776;

  block32776:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true32776to32878, false32776to32793;

  true32776to32878:
    assume local33286 == stack0o;
    goto block32878;

  false32776to32793:
    assume local33286 != stack0o;
    goto block32793;

  block32878:
    goto block32895;

  block32793:
    // ----- is instance
    // ----- branch
    goto true32793to32878, false32793to32810;

  true32793to32878:
    assume $As(local33286, Microsoft.Contracts.ICheckedException) != null;
    goto block32878;

  false32793to32810:
    assume $As(local33286, Microsoft.Contracts.ICheckedException) == null;
    goto block32810;

  block32810:
    // ----- branch
    goto block32827;

  block32895:
    // ----- classic pack  ----- BasicMethodology.ssc(162,5)
    assert temp3 != null;
    assert $Heap[temp3, $inv] == C && $Heap[temp3, $localinv] == $typeof(temp3);
    assert $Heap[temp3, CS.f] != 0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp3 && $Heap[$p, $ownerFrame] == CS ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp3, $inv] := CS;
    assume IsHeap($Heap);
    goto block32827;

  block32827:
    goto block32844;

  block32844:
    goto block32861;

  block32861:
    // ----- nop
    // ----- branch
    goto block32419;

  block32419:
    goto block32436;

  block32436:
    goto block32453;

  block32453:
    // ----- return  ----- BasicMethodology.ssc(163,3)
    return;

}



procedure CS..cctor();
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



implementation CS..cctor()
{

  entry:
    goto block33813;

  block33813:
    goto block33932;

  block33932:
    // ----- nop
    goto block33949;

  block33949:
    goto block33966;

  block33966:
    // ----- return
    return;

}


