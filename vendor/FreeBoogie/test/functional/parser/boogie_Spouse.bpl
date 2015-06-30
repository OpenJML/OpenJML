// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify Spouse.dll

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

const Person.spouse: <ref>name;

const Person.possn: <ref>name;

const System.Collections.IEnumerable: name;

const Possession: name;

const System.IComparable: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Reflection.IReflect: name;

const System.Runtime.InteropServices._Exception: name;

const System.Runtime.InteropServices._Type: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.IEquatable`1...System.String: name;

const Microsoft.Contracts.GuardException: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.IComparable`1...System.String: name;

const System.Runtime.Serialization.ISerializable: name;

const Person: name;

const Microsoft.Contracts.ICheckedException: name;

const System.ICloneable: name;

const System.Boolean: name;

const System.Exception: name;

const System.Reflection.MemberInfo: name;

const System.IConvertible: name;

axiom !IsStaticField(Person.spouse);

axiom IsDirectlyModifiableField(Person.spouse);

axiom AsPeerField(Person.spouse) == Person.spouse;

axiom DeclType(Person.spouse) == Person;

axiom AsRefField(Person.spouse, Person) == Person.spouse;

axiom !IsStaticField(Person.possn);

axiom IsDirectlyModifiableField(Person.possn);

axiom AsRepField(Person.possn, Person) == Person.possn;

axiom DeclType(Person.possn) == Person;

axiom AsRefField(Person.possn, Possession) == Person.possn;

axiom Person <: Person;

axiom $BaseClass(Person) == System.Object;

axiom Person <: $BaseClass(Person) && AsDirectSubClass(Person, $BaseClass(Person)) == Person;

axiom !$IsImmutable(Person) && $AsMutable(Person) == Person;

axiom (forall $U: name :: { $U <: Person } $U <: Person ==> $U == Person);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Person } IsHeap($h) && $h[$oi, $inv] <: Person && $h[$oi, $localinv] != System.Object ==> $h[$oi, Person.spouse] != null ==> $h[$h[$oi, Person.spouse], Person.spouse] == $oi);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Person.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Person.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack1o: ref, stack0b: bool, local0: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block1700;

  block1700:
    goto block1717;

  block1717:
    // ----- load field  ----- Spouse.ssc(11,3)
    assert this != null;
    stack0o := $Heap[this, Person.spouse];
    stack1o := null;
    // ----- binary operator  ----- Spouse.ssc(11,3)
    // ----- branch  ----- Spouse.ssc(11,3)
    goto true1717to1802, false1717to1734;

  true1717to1802:
    assume stack0o == stack1o;
    goto block1802;

  false1717to1734:
    assume stack0o != stack1o;
    goto block1734;

  block1802:
    // ----- load constant 1
    stack0b := true;
    goto block1819;

  block1734:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Person.spouse];
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, Person.spouse];
    // ----- binary operator
    // ----- branch
    goto true1734to1768, false1734to1751;

  true1734to1768:
    assume stack0o == this;
    goto block1768;

  false1734to1751:
    assume stack0o != this;
    goto block1751;

  block1768:
    // ----- load constant 1
    stack0b := true;
    goto block1785;

  block1751:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block1785;

  block1819:
    // ----- branch (no expression improvement)
    goto true1819to1921, false1819to1836;

  true1819to1921:
    assume stack0b;
    goto block1921;

  false1819to1836:
    assume !stack0b;
    goto block1836;

  block1921:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block1938;

  block1836:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true1836to1887, false1836to1853;

  block1785:
    // ----- branch
    goto block1819;

  true1836to1887:
    assume !stack0b;
    goto block1887;

  false1836to1853:
    assume stack0b;
    goto block1853;

  block1887:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block1938;

  block1853:
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

  block1938:
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



procedure Person.Marry$Person$notnull(this: ref, p$in: ref where $IsNotNull(p$in, Person));
  requires $Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in != this;
  requires $Heap[this, Person.spouse] == null;
  requires $Heap[p$in, Person.spouse] == null;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[p$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[p$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[p$in, $ownerFrame])) && old(($o != this || $f != Person.spouse) && ($o != p$in || $f != Person.spouse)) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.Marry$Person$notnull(this: ref, p$in: ref)
{
  var p: ref where $IsNotNull(p, Person), temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block3298;

  block3298:
    goto block3655;

  block3655:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(20,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(20,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block3672;

  block3672:
    // ----- FrameGuard processing  ----- Spouse.ssc(21,24)
    temp2 := p;
    // ----- classic unpack  ----- Spouse.ssc(21,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Person && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block3689;

  block3689:
    // ----- store field  ----- Spouse.ssc(22,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(23,9)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- branch
    goto block3825;

  block3825:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3825to3893, false3825to3842;

  true3825to3893:
    assume local4 == stack0o;
    goto block3893;

  false3825to3842:
    assume local4 != stack0o;
    goto block3842;

  block3893:
    // ----- classic pack  ----- Spouse.ssc(24,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Person.spouse] != null ==> $Heap[$Heap[temp2, Person.spouse], Person.spouse] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Person;
    assume IsHeap($Heap);
    goto block3876;

  block3842:
    // ----- is instance
    // ----- branch
    goto true3842to3893, false3842to3859;

  true3842to3893:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block3893;

  false3842to3859:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block3859;

  block3859:
    // ----- branch
    goto block3876;

  block3876:
    // ----- nop
    // ----- branch
    goto block3740;

  block3740:
    // ----- branch
    goto block3995;

  block3995:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3995to4063, false3995to4012;

  true3995to4063:
    assume local2 == stack0o;
    goto block4063;

  false3995to4012:
    assume local2 != stack0o;
    goto block4012;

  block4063:
    // ----- classic pack  ----- Spouse.ssc(25,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block4046;

  block4012:
    // ----- is instance
    // ----- branch
    goto true4012to4063, false4012to4029;

  true4012to4063:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block4063;

  false4012to4029:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block4029;

  block4029:
    // ----- branch
    goto block4046;

  block4046:
    // ----- nop
    // ----- branch
    goto block3791;

  block3791:
    // ----- return
    return;

}



axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure Person.MarryAssignTheOtherWayAround$Person$notnull(this: ref, p$in: ref where $IsNotNull(p$in, Person));
  requires $Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in != this;
  requires $Heap[this, Person.spouse] == null;
  requires $Heap[p$in, Person.spouse] == null;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[p$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[p$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[p$in, $ownerFrame])) && old(($o != this || $f != Person.spouse) && ($o != p$in || $f != Person.spouse)) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.MarryAssignTheOtherWayAround$Person$notnull(this: ref, p$in: ref)
{
  var p: ref where $IsNotNull(p, Person), temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block5831;

  block5831:
    goto block6188;

  block6188:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(35,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(35,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block6205;

  block6205:
    // ----- FrameGuard processing  ----- Spouse.ssc(36,24)
    temp2 := p;
    // ----- classic unpack  ----- Spouse.ssc(36,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Person && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block6222;

  block6222:
    // ----- store field  ----- Spouse.ssc(38,9)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(39,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- branch
    goto block6358;

  block6358:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true6358to6426, false6358to6375;

  true6358to6426:
    assume local4 == stack0o;
    goto block6426;

  false6358to6375:
    assume local4 != stack0o;
    goto block6375;

  block6426:
    // ----- classic pack  ----- Spouse.ssc(40,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Person.spouse] != null ==> $Heap[$Heap[temp2, Person.spouse], Person.spouse] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Person;
    assume IsHeap($Heap);
    goto block6409;

  block6375:
    // ----- is instance
    // ----- branch
    goto true6375to6426, false6375to6392;

  true6375to6426:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block6426;

  false6375to6392:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block6392;

  block6392:
    // ----- branch
    goto block6409;

  block6409:
    // ----- nop
    // ----- branch
    goto block6273;

  block6273:
    // ----- branch
    goto block6528;

  block6528:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true6528to6596, false6528to6545;

  true6528to6596:
    assume local2 == stack0o;
    goto block6596;

  false6528to6545:
    assume local2 != stack0o;
    goto block6545;

  block6596:
    // ----- classic pack  ----- Spouse.ssc(41,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block6579;

  block6545:
    // ----- is instance
    // ----- branch
    goto true6545to6596, false6545to6562;

  true6545to6596:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block6596;

  false6545to6562:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block6562;

  block6562:
    // ----- branch
    goto block6579;

  block6579:
    // ----- nop
    // ----- branch
    goto block6324;

  block6324:
    // ----- return
    return;

}



procedure Person.MarryAssignTheOtherWayAround_GoodnessRestored$Person$notnull$System.Boolean(this: ref, p$in: ref where $IsNotNull(p$in, Person), coinFlip$in: bool where true);
  requires $Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  free requires true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in != this;
  requires $Heap[this, Person.spouse] == null;
  requires $Heap[p$in, Person.spouse] == null;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[p$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[p$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[p$in, $ownerFrame])) && old(($o != this || $f != Person.spouse) && ($o != p$in || $f != Person.spouse)) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.MarryAssignTheOtherWayAround_GoodnessRestored$Person$notnull$System.Boolean(this: ref, p$in: ref, coinFlip$in: bool)
{
  var p: ref where $IsNotNull(p, Person), coinFlip: bool where true, temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    coinFlip := coinFlip$in;
    goto block8415;

  block8415:
    goto block8772;

  block8772:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(54,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(54,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block8789;

  block8789:
    // ----- FrameGuard processing  ----- Spouse.ssc(55,24)
    temp2 := p;
    // ----- classic unpack  ----- Spouse.ssc(55,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Person && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block8806;

  block8806:
    // ----- copy  ----- Spouse.ssc(57,9)
    stack0o := p;
    // ----- copy  ----- Spouse.ssc(57,9)
    stack1o := this;
    // ----- Owner.AssignSame  ----- Spouse.ssc(57,9)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- copy  ----- Spouse.ssc(58,9)
    stack0b := coinFlip;
    // ----- unary operator  ----- Spouse.ssc(58,9)
    // ----- branch  ----- Spouse.ssc(58,9)
    goto true8806to8840, false8806to8823;

  true8806to8840:
    assume !stack0b;
    goto block8840;

  false8806to8823:
    assume stack0b;
    goto block8823;

  block8840:
    // ----- store field  ----- Spouse.ssc(62,11)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(63,11)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- nop  ----- Spouse.ssc(65,7)
    goto block8857;

  block8823:
    // ----- store field  ----- Spouse.ssc(59,11)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(60,11)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- branch  ----- Spouse.ssc(61,11)
    goto block8857;

  block8857:
    // ----- branch
    goto block8993;

  block8993:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true8993to9061, false8993to9010;

  true8993to9061:
    assume local4 == stack0o;
    goto block9061;

  false8993to9010:
    assume local4 != stack0o;
    goto block9010;

  block9061:
    // ----- classic pack  ----- Spouse.ssc(65,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Person.spouse] != null ==> $Heap[$Heap[temp2, Person.spouse], Person.spouse] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Person;
    assume IsHeap($Heap);
    goto block9044;

  block9010:
    // ----- is instance
    // ----- branch
    goto true9010to9061, false9010to9027;

  true9010to9061:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block9061;

  false9010to9027:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block9027;

  block9027:
    // ----- branch
    goto block9044;

  block9044:
    // ----- nop
    // ----- branch
    goto block8908;

  block8908:
    // ----- branch
    goto block9163;

  block9163:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9163to9231, false9163to9180;

  true9163to9231:
    assume local2 == stack0o;
    goto block9231;

  false9163to9180:
    assume local2 != stack0o;
    goto block9180;

  block9231:
    // ----- classic pack  ----- Spouse.ssc(66,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block9214;

  block9180:
    // ----- is instance
    // ----- branch
    goto true9180to9231, false9180to9197;

  true9180to9231:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block9231;

  false9180to9197:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block9197;

  block9197:
    // ----- branch
    goto block9214;

  block9214:
    // ----- nop
    // ----- branch
    goto block8959;

  block8959:
    // ----- return
    return;

}



procedure Person.Marry_CaptureThis$Person$notnull(this: ref, p$in: ref where $IsNotNull(p$in, Person));
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in != this;
  requires $Heap[this, Person.spouse] == null;
  requires $Heap[p$in, Person.spouse] == null;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[this, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[this, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) && old(($o != this || $f != Person.spouse) && ($o != p$in || $f != Person.spouse)) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.Marry_CaptureThis$Person$notnull(this: ref, p$in: ref)
{
  var p: ref where $IsNotNull(p, Person), temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block11135;

  block11135:
    goto block11492;

  block11492:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(77,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(77,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block11509;

  block11509:
    // ----- FrameGuard processing  ----- Spouse.ssc(78,24)
    temp2 := p;
    // ----- classic unpack  ----- Spouse.ssc(78,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Person && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block11526;

  block11526:
    // ----- store field  ----- Spouse.ssc(79,9)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(80,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- branch
    goto block11662;

  block11662:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11662to11730, false11662to11679;

  true11662to11730:
    assume local4 == stack0o;
    goto block11730;

  false11662to11679:
    assume local4 != stack0o;
    goto block11679;

  block11730:
    // ----- classic pack  ----- Spouse.ssc(81,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Person.spouse] != null ==> $Heap[$Heap[temp2, Person.spouse], Person.spouse] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Person;
    assume IsHeap($Heap);
    goto block11713;

  block11679:
    // ----- is instance
    // ----- branch
    goto true11679to11730, false11679to11696;

  true11679to11730:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block11730;

  false11679to11696:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block11696;

  block11696:
    // ----- branch
    goto block11713;

  block11713:
    // ----- nop
    // ----- branch
    goto block11577;

  block11577:
    // ----- branch
    goto block11832;

  block11832:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11832to11900, false11832to11849;

  true11832to11900:
    assume local2 == stack0o;
    goto block11900;

  false11832to11849:
    assume local2 != stack0o;
    goto block11849;

  block11900:
    // ----- classic pack  ----- Spouse.ssc(82,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block11883;

  block11849:
    // ----- is instance
    // ----- branch
    goto true11849to11900, false11849to11866;

  true11849to11900:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block11900;

  false11849to11866:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block11866;

  block11866:
    // ----- branch
    goto block11883;

  block11883:
    // ----- nop
    // ----- branch
    goto block11628;

  block11628:
    // ----- return
    return;

}



procedure Person.Marry_CaptureEither$Person$notnull(this: ref, p$in: ref where $IsNotNull(p$in, Person));
  requires $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  requires $Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  // user-declared preconditions
  requires p$in != this;
  requires $Heap[this, Person.spouse] == null;
  requires $Heap[p$in, Person.spouse] == null;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[this, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[this, $ownerFrame]) && (old($Heap)[$o, $ownerRef] != old($Heap)[p$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[p$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && (old($Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame]) || old($Heap[$o, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[p$in, $ownerFrame]))) && old(($o != this || $f != Person.spouse) && ($o != p$in || $f != Person.spouse)) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.Marry_CaptureEither$Person$notnull(this: ref, p$in: ref)
{
  var p: ref where $IsNotNull(p, Person), temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block13617;

  block13617:
    goto block13923;

  block13923:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(92,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(92,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block13940;

  block13940:
    // ----- FrameGuard processing  ----- Spouse.ssc(93,24)
    temp2 := p;
    // ----- classic unpack  ----- Spouse.ssc(93,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Person && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block13957;

  block13957:
    // ----- store field  ----- Spouse.ssc(94,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Person) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == this ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, Person.spouse] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- store field  ----- Spouse.ssc(95,9)
    assert p != null;
    assert !($Heap[p, $inv] <: Person) || $Heap[p, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Person && $Heap[$o, Person.spouse] == p ==> !($Heap[$o, $inv] <: Person) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, Person.spouse] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- branch
    goto block14093;

  block14093:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14093to14161, false14093to14110;

  true14093to14161:
    assume local4 == stack0o;
    goto block14161;

  false14093to14110:
    assume local4 != stack0o;
    goto block14110;

  block14161:
    // ----- classic pack  ----- Spouse.ssc(96,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Person.spouse] != null ==> $Heap[$Heap[temp2, Person.spouse], Person.spouse] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Person;
    assume IsHeap($Heap);
    goto block14144;

  block14110:
    // ----- is instance
    // ----- branch
    goto true14110to14161, false14110to14127;

  true14110to14161:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block14161;

  false14110to14127:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block14127;

  block14127:
    // ----- branch
    goto block14144;

  block14144:
    // ----- nop
    // ----- branch
    goto block14008;

  block14008:
    // ----- branch
    goto block14263;

  block14263:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14263to14331, false14263to14280;

  true14263to14331:
    assume local2 == stack0o;
    goto block14331;

  false14263to14280:
    assume local2 != stack0o;
    goto block14280;

  block14331:
    // ----- classic pack  ----- Spouse.ssc(97,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block14314;

  block14280:
    // ----- is instance
    // ----- branch
    goto true14280to14331, false14280to14297;

  true14280to14331:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block14331;

  false14280to14297:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block14297;

  block14297:
    // ----- branch
    goto block14314;

  block14314:
    // ----- nop
    // ----- branch
    goto block14059;

  block14059:
    // ----- return
    return;

}



procedure Person.MM(this: ref);
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



implementation Person.MM(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    goto block15827;

  block15827:
    goto block15929;

  block15929:
    // ----- nop
    // ----- load field  ----- Spouse.ssc(101,5)
    assert this != null;
    stack0o := $Heap[this, Person.spouse];
    stack1o := null;
    // ----- binary operator  ----- Spouse.ssc(101,5)
    // ----- branch  ----- Spouse.ssc(101,5)
    goto true15929to16048, false15929to15946;

  true15929to16048:
    assume stack0o == stack1o;
    goto block16048;

  false15929to15946:
    assume stack0o != stack1o;
    goto block15946;

  block16048:
    // ----- return
    return;

  block15946:
    // ----- serialized AssertStatement  ----- Spouse.ssc(102,7)
    assert $Heap[this, $ownerRef] == $Heap[$Heap[this, Person.spouse], $ownerRef] && $Heap[this, $ownerFrame] == $Heap[$Heap[this, Person.spouse], $ownerFrame];
    goto block16031;

  block16031:
    // ----- nop
    goto block16048;

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

procedure Person.NN(this: ref);
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



implementation Person.NN(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    goto block16915;

  block16915:
    goto block17017;

  block17017:
    // ----- nop
    // ----- load field  ----- Spouse.ssc(107,5)
    assert this != null;
    stack0o := $Heap[this, Person.possn];
    stack1o := null;
    // ----- binary operator  ----- Spouse.ssc(107,5)
    // ----- branch  ----- Spouse.ssc(107,5)
    goto true17017to17136, false17017to17034;

  true17017to17136:
    assume stack0o == stack1o;
    goto block17136;

  false17017to17034:
    assume stack0o != stack1o;
    goto block17034;

  block17136:
    // ----- return
    return;

  block17034:
    // ----- serialized AssertStatement  ----- Spouse.ssc(108,7)
    assert $Heap[$Heap[this, Person.possn], $ownerRef] == this && $Heap[$Heap[this, Person.possn], $ownerFrame] == TypeName(TypeObject(Person));
    goto block17119;

  block17119:
    // ----- nop
    goto block17136;

}



axiom Possession <: Possession;

axiom $BaseClass(Possession) == System.Object;

axiom Possession <: $BaseClass(Possession) && AsDirectSubClass(Possession, $BaseClass(Possession)) == Possession;

axiom !$IsImmutable(Possession) && $AsMutable(Possession) == Possession;

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

procedure Person.PP(this: ref);
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



implementation Person.PP(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack50000o: ref, stack0o: ref, o: ref where $Is(o, System.Object), stack1o: ref, stack2s: struct, stack2o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    goto block17935;

  block17935:
    goto block18088;

  block18088:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(113,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(113,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block18105;

  block18105:
    // ----- new object  ----- Spouse.ssc(114,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == System.Object;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Spouse.ssc(114,7)
    assert stack50000o != null;
    call System.Object..ctor(stack50000o);
    // ----- copy  ----- Spouse.ssc(114,7)
    stack0o := stack50000o;
    // ----- copy  ----- Spouse.ssc(114,7)
    o := stack0o;
    // ----- copy  ----- Spouse.ssc(115,7)
    stack0o := o;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- copy  ----- Spouse.ssc(115,7)
    stack1o := this;
    // ----- load token  ----- Spouse.ssc(115,7)
    havoc stack2s;
    assume $IsTokenForType(stack2s, Person);
    // ----- statically resolved GetTypeFromHandle call  ----- Spouse.ssc(115,7)
    stack2o := TypeObject(Person);
    // ----- Owner.Assign  ----- Spouse.ssc(115,7)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- serialized AssertStatement  ----- Spouse.ssc(116,7)
    assert $Heap[o, $ownerRef] == this && $Heap[o, $ownerFrame] == TypeName(TypeObject(Person));
    goto block18190;

  block18190:
    // ----- nop
    // ----- branch
    goto block18275;

  block18275:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true18275to18343, false18275to18292;

  true18275to18343:
    assume local2 == stack0o;
    goto block18343;

  false18275to18292:
    assume local2 != stack0o;
    goto block18292;

  block18343:
    // ----- classic pack  ----- Spouse.ssc(117,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block18326;

  block18292:
    // ----- is instance
    // ----- branch
    goto true18292to18343, false18292to18309;

  true18292to18343:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block18343;

  false18292to18309:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block18309;

  block18309:
    // ----- branch
    goto block18326;

  block18326:
    // ----- nop
    // ----- branch
    goto block18241;

  block18241:
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



procedure Person.A0$System.Object$notnull(this: ref, subject$in: ref where $IsNotNull(subject$in, System.Object));
  free requires $Heap[subject$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Person.A0$System.Object$notnull(this: ref, subject$in: ref)
{
  var subject: ref where $IsNotNull(subject, System.Object), stack0o: ref, stack1o: ref, stack2s: struct, stack2o: ref;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    subject := subject$in;
    goto block19278;

  block19278:
    goto block19380;

  block19380:
    // ----- nop
    // ----- copy  ----- Spouse.ssc(121,5)
    stack0o := subject;
    // ----- copy  ----- Spouse.ssc(121,5)
    stack1o := this;
    // ----- load token  ----- Spouse.ssc(121,5)
    havoc stack2s;
    assume $IsTokenForType(stack2s, Person);
    // ----- statically resolved GetTypeFromHandle call  ----- Spouse.ssc(121,5)
    stack2o := TypeObject(Person);
    // ----- Owner.Assign  ----- Spouse.ssc(121,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- return
    return;

}



procedure Person.A1$Possession$notnull(this: ref, subject$in: ref where $IsNotNull(subject$in, Possession));
  requires $Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[subject$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[subject$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[subject$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[subject$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.A1$Possession$notnull(this: ref, subject$in: ref)
{
  var subject: ref where $IsNotNull(subject, Possession), stack0o: ref, stack1o: ref, stack2s: struct, stack2o: ref;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    subject := subject$in;
    goto block19754;

  block19754:
    goto block19856;

  block19856:
    // ----- nop
    // ----- copy  ----- Spouse.ssc(125,5)
    stack0o := subject;
    // ----- copy  ----- Spouse.ssc(125,5)
    stack1o := this;
    // ----- load token  ----- Spouse.ssc(125,5)
    havoc stack2s;
    assume $IsTokenForType(stack2s, System.String);
    // ----- statically resolved GetTypeFromHandle call  ----- Spouse.ssc(125,5)
    stack2o := TypeObject(System.String);
    // ----- Owner.Assign  ----- Spouse.ssc(125,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- return
    return;

}



procedure Person.A2$Possession$notnull(this: ref, subject$in: ref where $IsNotNull(subject$in, Possession));
  requires $Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[subject$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[subject$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[subject$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[subject$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.A2$Possession$notnull(this: ref, subject$in: ref)
{
  var subject: ref where $IsNotNull(subject, Possession), stack0o: ref, stack1o: ref, stack2s: struct, stack2o: ref;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    subject := subject$in;
    goto block20230;

  block20230:
    goto block20332;

  block20332:
    // ----- nop
    // ----- copy  ----- Spouse.ssc(129,5)
    stack0o := subject;
    // ----- copy  ----- Spouse.ssc(129,5)
    stack1o := this;
    // ----- load token  ----- Spouse.ssc(129,5)
    havoc stack2s;
    assume $IsTokenForType(stack2s, Person);
    // ----- statically resolved GetTypeFromHandle call  ----- Spouse.ssc(129,5)
    stack2o := TypeObject(Person);
    // ----- Owner.Assign  ----- Spouse.ssc(129,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- return
    return;

}



procedure Person.A3$Possession$notnull(this: ref, subject$in: ref where $IsNotNull(subject$in, Possession));
  requires $Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[subject$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && !($Heap[this, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[subject$in, $ownerFrame]);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[subject$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[subject$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[subject$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person.A3$Possession$notnull(this: ref, subject$in: ref)
{
  var subject: ref where $IsNotNull(subject, Possession), temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack0o: ref, stack1o: ref, stack2s: struct, stack2o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    subject := subject$in;
    goto block21012;

  block21012:
    goto block21233;

  block21233:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(135,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(135,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block21250;

  block21250:
    // ----- copy  ----- Spouse.ssc(136,7)
    stack0o := subject;
    // ----- copy  ----- Spouse.ssc(136,7)
    stack1o := this;
    // ----- load token  ----- Spouse.ssc(136,7)
    havoc stack2s;
    assume $IsTokenForType(stack2s, Person);
    // ----- statically resolved GetTypeFromHandle call  ----- Spouse.ssc(136,7)
    stack2o := TypeObject(Person);
    // ----- Owner.Assign  ----- Spouse.ssc(136,7)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- branch
    goto block21335;

  block21335:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true21335to21403, false21335to21352;

  true21335to21403:
    assume local2 == stack0o;
    goto block21403;

  false21335to21352:
    assume local2 != stack0o;
    goto block21352;

  block21403:
    // ----- classic pack  ----- Spouse.ssc(137,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block21386;

  block21352:
    // ----- is instance
    // ----- branch
    goto true21352to21403, false21352to21369;

  true21352to21403:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block21403;

  false21352to21369:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block21369;

  block21369:
    // ----- branch
    goto block21386;

  block21386:
    // ----- nop
    // ----- branch
    goto block21301;

  block21301:
    // ----- return
    return;

}



procedure Person.B0$System.Object$notnull(this: ref, subject$in: ref where $IsNotNull(subject$in, System.Object));
  free requires $Heap[subject$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[subject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[subject$in, $ownerRef], $inv] <: $Heap[subject$in, $ownerFrame]) || $Heap[$Heap[subject$in, $ownerRef], $localinv] == $BaseClass($Heap[subject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[subject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[subject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Person.B0$System.Object$notnull(this: ref, subject$in: ref)
{
  var subject: ref where $IsNotNull(subject, System.Object), stack0o: ref, stack1o: ref;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    subject := subject$in;
    goto block22270;

  block22270:
    goto block22372;

  block22372:
    // ----- nop
    // ----- copy  ----- Spouse.ssc(141,5)
    stack0o := subject;
    // ----- copy  ----- Spouse.ssc(141,5)
    stack1o := this;
    // ----- Owner.AssignSame  ----- Spouse.ssc(141,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- serialized AssumeStatement  ----- Spouse.ssc(142,5)
    assume false;
    return;

}



procedure Person.B1(this: ref);
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



implementation Person.B1(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool, stack50000o: ref, subject: ref where $Is(subject, System.Object);

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    goto block22933;

  block22933:
    goto block23035;

  block23035:
    // ----- nop
    // ----- load field  ----- Spouse.ssc(146,5)
    assert this != null;
    stack0o := $Heap[this, Person.possn];
    stack1o := null;
    // ----- binary operator  ----- Spouse.ssc(146,5)
    // ----- branch  ----- Spouse.ssc(146,5)
    goto true23035to23069, false23035to23052;

  true23035to23069:
    assume stack0o == stack1o;
    goto block23069;

  false23035to23052:
    assume stack0o != stack1o;
    goto block23052;

  block23069:
    // ----- return
    return;

  block23052:
    // ----- new object  ----- Spouse.ssc(147,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == System.Object;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Spouse.ssc(147,7)
    assert stack50000o != null;
    call System.Object..ctor(stack50000o);
    // ----- copy  ----- Spouse.ssc(147,7)
    stack0o := stack50000o;
    // ----- copy  ----- Spouse.ssc(147,7)
    subject := stack0o;
    // ----- copy  ----- Spouse.ssc(148,7)
    stack0o := subject;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- load field  ----- Spouse.ssc(148,7)
    assert this != null;
    stack1o := $Heap[this, Person.possn];
    assert stack1o != null;
    stack1o := stack1o;
    // ----- Owner.AssignSame  ----- Spouse.ssc(148,7)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    goto block23069;

}



procedure Person.B2(this: ref);
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



implementation Person.B2(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack0o: ref, stack1o: ref, stack0b: bool, stack50000o: ref, subject: ref where $Is(subject, System.Object);

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    goto block23851;

  block23851:
    goto block24004;

  block24004:
    // ----- nop
    // ----- FrameGuard processing  ----- Spouse.ssc(153,22)
    temp0 := this;
    // ----- classic unpack  ----- Spouse.ssc(153,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Person && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block24021;

  block24021:
    // ----- load field  ----- Spouse.ssc(154,7)
    assert this != null;
    stack0o := $Heap[this, Person.possn];
    stack1o := null;
    // ----- binary operator  ----- Spouse.ssc(154,7)
    // ----- branch  ----- Spouse.ssc(154,7)
    goto true24021to24055, false24021to24038;

  true24021to24055:
    assume stack0o == stack1o;
    goto block24055;

  false24021to24038:
    assume stack0o != stack1o;
    goto block24038;

  block24055:
    // ----- branch
    goto block24140;

  block24038:
    // ----- new object  ----- Spouse.ssc(155,9)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == System.Object;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Spouse.ssc(155,9)
    assert stack50000o != null;
    call System.Object..ctor(stack50000o);
    // ----- copy  ----- Spouse.ssc(155,9)
    stack0o := stack50000o;
    // ----- copy  ----- Spouse.ssc(155,9)
    subject := stack0o;
    // ----- copy  ----- Spouse.ssc(156,9)
    stack0o := subject;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- load field  ----- Spouse.ssc(156,9)
    assert this != null;
    stack1o := $Heap[this, Person.possn];
    assert stack1o != null;
    stack1o := stack1o;
    // ----- Owner.AssignSame  ----- Spouse.ssc(156,9)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    goto block24055;

  block24140:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true24140to24208, false24140to24157;

  true24140to24208:
    assume local2 == stack0o;
    goto block24208;

  false24140to24157:
    assume local2 != stack0o;
    goto block24157;

  block24208:
    // ----- classic pack  ----- Spouse.ssc(158,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    goto block24191;

  block24157:
    // ----- is instance
    // ----- branch
    goto true24157to24208, false24157to24174;

  true24157to24208:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block24208;

  false24157to24174:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block24174;

  block24174:
    // ----- branch
    goto block24191;

  block24191:
    // ----- nop
    // ----- branch
    goto block24106;

  block24106:
    // ----- return
    return;

}



procedure Person..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Person && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Person <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Person..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, Person);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, Person.possn] == null;
    assume $Heap[this, Person.spouse] == null;
    goto block25092;

  block25092:
    goto block25109;

  block25109:
    // ----- call  ----- Spouse.ssc(7,21)
    assert this != null;
    call System.Object..ctor(this);
    goto block25177;

  block25177:
    // ----- FrameGuard processing  ----- Spouse.ssc(7,26)
    temp0 := this;
    // ----- classic pack  ----- Spouse.ssc(7,26)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Person.spouse] != null ==> $Heap[$Heap[temp0, Person.spouse], Person.spouse] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Person ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Person;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure Person..cctor();
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



implementation Person..cctor()
{

  entry:
    goto block25466;

  block25466:
    goto block25517;

  block25517:
    // ----- nop
    // ----- return
    return;

}



procedure Possession..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Possession && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Possession <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Possession..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Possession);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block25721;

  block25721:
    goto block25738;

  block25738:
    // ----- call  ----- Spouse.ssc(162,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Possession ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Possession;
    assume IsHeap($Heap);
    return;

}


