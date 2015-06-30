// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify VisibilityBasedInvariants.dll

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

const Thing.f: <ref>name;

const Friend.th: <ref>name;

const Thing.y: <int>name;

const Friend.x: <int>name;

const System.Reflection.IReflect: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const Thing: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Runtime.InteropServices._Exception: name;

const System.Runtime.Serialization.ISerializable: name;

const Microsoft.Contracts.GuardException: name;

const Microsoft.Contracts.ICheckedException: name;

const System.Exception: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Boolean: name;

const System.Runtime.InteropServices._Type: name;

const Friend: name;

const System.Reflection.MemberInfo: name;

axiom !IsStaticField(Friend.th);

axiom IsDirectlyModifiableField(Friend.th);

axiom DeclType(Friend.th) == Friend;

axiom AsRefField(Friend.th, Thing) == Friend.th;

axiom !IsStaticField(Thing.f);

axiom IsDirectlyModifiableField(Thing.f);

axiom AsPeerField(Thing.f) == Thing.f;

axiom DeclType(Thing.f) == Thing;

axiom AsRefField(Thing.f, Friend) == Thing.f;

axiom !IsStaticField(Thing.y);

axiom IsDirectlyModifiableField(Thing.y);

axiom DeclType(Thing.y) == Thing;

axiom AsRangeField(Thing.y, System.Int32) == Thing.y;

axiom !IsStaticField(Friend.x);

axiom IsDirectlyModifiableField(Friend.x);

axiom DeclType(Friend.x) == Friend;

axiom AsRangeField(Friend.x, System.Int32) == Friend.x;

axiom Friend <: Friend;

axiom $BaseClass(Friend) == System.Object;

axiom Friend <: $BaseClass(Friend) && AsDirectSubClass(Friend, $BaseClass(Friend)) == Friend;

axiom !$IsImmutable(Friend) && $AsMutable(Friend) == Friend;

axiom (forall $U: name :: { $U <: Friend } $U <: Friend ==> $U == Friend);

axiom Thing <: Thing;

axiom $BaseClass(Thing) == System.Object;

axiom Thing <: $BaseClass(Thing) && AsDirectSubClass(Thing, $BaseClass(Thing)) == Thing;

axiom !$IsImmutable(Thing) && $AsMutable(Thing) == Thing;

axiom (forall $U: name :: { $U <: Thing } $U <: Thing ==> $U == Thing);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Thing } IsHeap($h) && $h[$oi, $inv] <: Thing && $h[$oi, $localinv] != System.Object ==> ($h[$oi, Thing.f] == null || $h[$h[$oi, Thing.f], Friend.th] == $oi) && 0 <= $h[$oi, Thing.y]);

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: Friend } IsHeap($h) && $h[$oi, $inv] <: Friend && $h[$oi, $localinv] != System.Object ==> $h[$oi, Friend.th] != null && $h[$oi, Friend.x] == $h[$h[$oi, Friend.th], Thing.y] && $h[$h[$oi, Friend.th], Thing.f] == $oi);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Friend.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Friend.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack1o: ref, stack0b: bool, stack0i: int, stack1i: int, stack50000o: ref, local0: bool where true, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Friend);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block1751;

  block1751:
    goto block1768;

  block1768:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(6,3)
    assert this != null;
    stack0o := $Heap[this, Friend.th];
    stack1o := null;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(6,3)
    // ----- branch  ----- VisibilityBasedInvariants.ssc(6,3)
    goto true1768to1870, false1768to1785;

  true1768to1870:
    assume stack0o != stack1o;
    goto block1870;

  false1768to1785:
    assume stack0o == stack1o;
    goto block1785;

  block1870:
    // ----- load field
    assert this != null;
    stack0i := $Heap[this, Friend.x];
    // ----- load field
    assert this != null;
    stack1o := $Heap[this, Friend.th];
    // ----- load field
    assert stack1o != null;
    stack1i := $Heap[stack1o, Thing.y];
    // ----- binary operator
    // ----- branch
    goto true1870to1972, false1870to1887;

  block1785:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true1785to1836, false1785to1802;

  true1785to1836:
    assume !stack0b;
    goto block1836;

  false1785to1802:
    assume stack0b;
    goto block1802;

  block1836:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block2091;

  block1802:
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

  true1870to1972:
    assume stack0i == stack1i;
    goto block1972;

  false1870to1887:
    assume stack0i != stack1i;
    goto block1887;

  block1972:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Friend.th];
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, Thing.f];
    // ----- binary operator
    // ----- branch
    goto true1972to2074, false1972to1989;

  block1887:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true1887to1938, false1887to1904;

  true1887to1938:
    assume !stack0b;
    goto block1938;

  false1887to1904:
    assume stack0b;
    goto block1904;

  block1938:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block2091;

  block1904:
    assume false;
    // ----- new object  ----- VisibilityBasedInvariants.ssc(7,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- VisibilityBasedInvariants.ssc(7,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- VisibilityBasedInvariants.ssc(7,3)
    stack0o := stack50000o;
    // ----- throw  ----- VisibilityBasedInvariants.ssc(7,3)
    assert stack0o != null;
    assume false;
    return;

  true1972to2074:
    assume stack0o == this;
    goto block2074;

  false1972to1989:
    assume stack0o != this;
    goto block1989;

  block2074:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block2091;

  block1989:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true1989to2040, false1989to2006;

  block2091:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

  true1989to2040:
    assume !stack0b;
    goto block2040;

  false1989to2006:
    assume stack0b;
    goto block2006;

  block2040:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block2091;

  block2006:
    assume false;
    // ----- new object  ----- VisibilityBasedInvariants.ssc(8,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- VisibilityBasedInvariants.ssc(8,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- VisibilityBasedInvariants.ssc(8,3)
    stack0o := stack50000o;
    // ----- throw  ----- VisibilityBasedInvariants.ssc(8,3)
    assert stack0o != null;
    assume false;
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



procedure Friend..ctor$Thing$notnull(this: ref, thing$in: ref where $IsNotNull(thing$in, Thing));
  requires $Heap[thing$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[thing$in, $allocated] == true;
  // user-declared preconditions
  requires $Heap[thing$in, Thing.f] == null;
  requires ($Heap[thing$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[thing$in, $ownerRef], $inv] <: $Heap[thing$in, $ownerFrame]) || $Heap[$Heap[thing$in, $ownerRef], $localinv] == $BaseClass($Heap[thing$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[thing$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[thing$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Friend && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[thing$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[thing$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Friend <: DeclType($f))) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[thing$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[thing$in, $ownerFrame])) && old($o != thing$in || $f != Thing.f) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Friend..ctor$Thing$notnull(this: ref, thing$in: ref)
{
  var thing: ref where $IsNotNull(thing, Thing), stack0o: ref, stack1o: ref, stack0i: int, temp0: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool, temp2: ref;

  entry:
    assume $IsNotNull(this, Friend);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    thing := thing$in;
    assume $Heap[this, Friend.x] == 0;
    assume $Heap[this, Friend.th] == null;
    goto block3332;

  block3332:
    goto block3485;

  block3485:
    // ----- nop
    // ----- call  ----- VisibilityBasedInvariants.ssc(12,5)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block3553;

  block3553:
    // ----- copy  ----- VisibilityBasedInvariants.ssc(15,5)
    stack0o := thing;
    // ----- copy  ----- VisibilityBasedInvariants.ssc(15,5)
    stack1o := this;
    // ----- Owner.AssignSame  ----- VisibilityBasedInvariants.ssc(15,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- store field  ----- VisibilityBasedInvariants.ssc(16,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Friend) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Thing && $Heap[$o, Thing.f] == this ==> !($Heap[$o, $inv] <: Thing) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Friend.th] := thing;
    assume IsHeap($Heap);
    // ----- load field  ----- VisibilityBasedInvariants.ssc(17,5)
    assert thing != null;
    stack0i := $Heap[thing, Thing.y];
    // ----- store field  ----- VisibilityBasedInvariants.ssc(17,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Friend) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(18,22)
    temp0 := thing;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(18,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block3570;

  block3570:
    // ----- store field  ----- VisibilityBasedInvariants.ssc(19,7)
    assert thing != null;
    assert !($Heap[thing, $inv] <: Thing) || $Heap[thing, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == thing ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[thing, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[thing, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[thing, $ownerRef], $inv] <: $Heap[thing, $ownerFrame]) || $Heap[$Heap[thing, $ownerRef], $localinv] == $BaseClass($Heap[thing, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[thing, $ownerRef] == $Heap[this, $ownerRef] && $Heap[thing, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[thing, Thing.f] := this;
    call $UpdateOwnersForPeer(thing, this);
    assume IsHeap($Heap);
    // ----- branch
    goto block3655;

  block3655:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3655to3723, false3655to3672;

  true3655to3723:
    assume local3 == stack0o;
    goto block3723;

  false3655to3672:
    assume local3 != stack0o;
    goto block3672;

  block3723:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(20,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block3706;

  block3672:
    // ----- is instance
    // ----- branch
    goto true3672to3723, false3672to3689;

  true3672to3723:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block3723;

  false3672to3689:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block3689;

  block3689:
    // ----- branch
    goto block3706;

  block3706:
    // ----- nop
    // ----- branch
    goto block3621;

  block3621:
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(21,3)
    temp2 := this;
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(21,3)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Friend.th] != null;
    assert $Heap[temp2, Friend.x] == $Heap[$Heap[temp2, Friend.th], Thing.y];
    assert $Heap[$Heap[temp2, Friend.th], Thing.f] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Friend;
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



axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure Friend..ctor$Thing$notnull$System.Boolean(this: ref, thing$in: ref where $IsNotNull(thing$in, Thing), disambiguator$in: bool where true);
  free requires $Heap[thing$in, $allocated] == true;
  free requires true;
  // user-declared preconditions
  requires $Heap[thing$in, Thing.f] == null;
  requires ($Heap[thing$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[thing$in, $ownerRef], $inv] <: $Heap[thing$in, $ownerFrame]) || $Heap[$Heap[thing$in, $ownerRef], $localinv] == $BaseClass($Heap[thing$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[thing$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[thing$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Friend && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[this, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[this, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Friend <: DeclType($f))) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame])) && old($o != thing$in || $f != Thing.f) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Friend..ctor$Thing$notnull$System.Boolean(this: ref, thing$in: ref, disambiguator$in: bool)
{
  var thing: ref where $IsNotNull(thing, Thing), disambiguator: bool where true, stack0o: ref, stack1o: ref, stack0i: int, temp0: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool, temp2: ref;

  entry:
    assume $IsNotNull(this, Friend);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    thing := thing$in;
    disambiguator := disambiguator$in;
    assume $Heap[this, Friend.x] == 0;
    assume $Heap[this, Friend.th] == null;
    goto block4930;

  block4930:
    goto block5083;

  block5083:
    // ----- nop
    // ----- call  ----- VisibilityBasedInvariants.ssc(25,5)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block5151;

  block5151:
    // ----- copy  ----- VisibilityBasedInvariants.ssc(28,5)
    stack0o := this;
    // ----- copy  ----- VisibilityBasedInvariants.ssc(28,5)
    stack1o := thing;
    // ----- Owner.AssignSame  ----- VisibilityBasedInvariants.ssc(28,5)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- store field  ----- VisibilityBasedInvariants.ssc(29,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Friend) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Thing && $Heap[$o, Thing.f] == this ==> !($Heap[$o, $inv] <: Thing) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Friend.th] := thing;
    assume IsHeap($Heap);
    // ----- load field  ----- VisibilityBasedInvariants.ssc(30,5)
    assert thing != null;
    stack0i := $Heap[thing, Thing.y];
    // ----- store field  ----- VisibilityBasedInvariants.ssc(30,5)
    assert this != null;
    assert !($Heap[this, $inv] <: Friend) || $Heap[this, $localinv] == System.Object;
    $Heap[this, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(31,22)
    temp0 := thing;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(31,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block5168;

  block5168:
    // ----- store field  ----- VisibilityBasedInvariants.ssc(32,7)
    assert thing != null;
    assert !($Heap[thing, $inv] <: Thing) || $Heap[thing, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == thing ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    assert this == null || ($Heap[thing, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[thing, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[thing, $ownerRef], $inv] <: $Heap[thing, $ownerFrame]) || $Heap[$Heap[thing, $ownerRef], $localinv] == $BaseClass($Heap[thing, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[thing, $ownerRef] == $Heap[this, $ownerRef] && $Heap[thing, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[thing, Thing.f] := this;
    call $UpdateOwnersForPeer(thing, this);
    assume IsHeap($Heap);
    // ----- branch
    goto block5253;

  block5253:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true5253to5321, false5253to5270;

  true5253to5321:
    assume local3 == stack0o;
    goto block5321;

  false5253to5270:
    assume local3 != stack0o;
    goto block5270;

  block5321:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(33,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block5304;

  block5270:
    // ----- is instance
    // ----- branch
    goto true5270to5321, false5270to5287;

  true5270to5321:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block5321;

  false5270to5287:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block5287;

  block5287:
    // ----- branch
    goto block5304;

  block5304:
    // ----- nop
    // ----- branch
    goto block5219;

  block5219:
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(34,3)
    temp2 := this;
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(34,3)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Friend.th] != null;
    assert $Heap[temp2, Friend.x] == $Heap[$Heap[temp2, Friend.th], Thing.y];
    assert $Heap[$Heap[temp2, Friend.th], Thing.f] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Friend;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure Friend..cctor();
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



implementation Friend..cctor()
{

  entry:
    goto block6443;

  block6443:
    goto block6494;

  block6494:
    // ----- nop
    // ----- return
    return;

}



procedure Thing.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation Thing.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack1o: ref, stack0b: bool, stack0i: int, stack1i: int, local0: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block6936;

  block6936:
    goto block6953;

  block6953:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(48,3)
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    stack1o := null;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(48,3)
    // ----- branch  ----- VisibilityBasedInvariants.ssc(48,3)
    goto true6953to7072, false6953to6970;

  true6953to7072:
    assume stack0o == stack1o;
    goto block7072;

  false6953to6970:
    assume stack0o != stack1o;
    goto block6970;

  block7072:
    // ----- load constant 0
    stack0i := 0;
    // ----- load field
    assert this != null;
    stack1i := $Heap[this, Thing.y];
    // ----- binary operator
    // ----- branch
    goto true7072to7174, false7072to7089;

  block6970:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    // ----- load field
    assert stack0o != null;
    stack0o := $Heap[stack0o, Friend.th];
    // ----- binary operator
    // ----- branch
    goto true6970to7072, false6970to6987;

  true6970to7072:
    assume stack0o == this;
    goto block7072;

  false6970to6987:
    assume stack0o != this;
    goto block6987;

  block6987:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true6987to7038, false6987to7004;

  true7072to7174:
    assume stack0i <= stack1i;
    goto block7174;

  false7072to7089:
    assume stack0i > stack1i;
    goto block7089;

  block7174:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block7191;

  block7089:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true7089to7140, false7089to7106;

  true6987to7038:
    assume !stack0b;
    goto block7038;

  false6987to7004:
    assume stack0b;
    goto block7004;

  block7038:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block7191;

  block7004:
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

  true7089to7140:
    assume !stack0b;
    goto block7140;

  false7089to7106:
    assume stack0b;
    goto block7106;

  block7140:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block7191;

  block7106:
    assume false;
    // ----- new object  ----- VisibilityBasedInvariants.ssc(51,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- VisibilityBasedInvariants.ssc(51,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- VisibilityBasedInvariants.ssc(51,3)
    stack0o := stack50000o;
    // ----- throw  ----- VisibilityBasedInvariants.ssc(51,3)
    assert stack0o != null;
    assume false;
    return;

  block7191:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

}



procedure Thing..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Thing && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Thing <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Thing..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, Thing.f] == null;
    assume $Heap[this, Thing.y] == 0;
    goto block7956;

  block7956:
    goto block7973;

  block7973:
    // ----- call  ----- VisibilityBasedInvariants.ssc(53,18)
    assert this != null;
    call System.Object..ctor(this);
    goto block8041;

  block8041:
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(53,19)
    temp0 := this;
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(53,19)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    // ----- return  ----- VisibilityBasedInvariants.ssc(53,19)
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

procedure Thing.P(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] != null && TypeObject($typeof($Heap[this, Thing.f])) == TypeObject(Friend);
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



implementation Thing.P(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack0o: ref, temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), local5: int where InRange(local5, System.Int32), stack0i: int, local6: ref where $Is(local6, Friend), local7: int where InRange(local7, System.Int32), stack0b: bool;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block8925;

  block8925:
    goto block9146;

  block9146:
    // ----- nop
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(67,22)
    temp0 := this;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(67,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block9163;

  block9163:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(68,24)
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(68,24)
    temp2 := stack0o;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(68,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Friend && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block9180;

  block9180:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(69,9)
    assert this != null;
    local5 := $Heap[this, Thing.y];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(69,9)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(69,9)
    stack0i := local5 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(69,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Thing) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == this ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Thing.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- load field  ----- VisibilityBasedInvariants.ssc(70,9)
    assert this != null;
    local6 := $Heap[this, Thing.f];
    // ----- load field  ----- VisibilityBasedInvariants.ssc(70,9)
    assert local6 != null;
    local7 := $Heap[local6, Friend.x];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(70,9)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(70,9)
    stack0i := local7 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(70,9)
    assert local6 != null;
    assert !($Heap[local6, $inv] <: Friend) || $Heap[local6, $localinv] == System.Object;
    $Heap[local6, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local7;
    // ----- branch
    goto block9316;

  block9316:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9316to9384, false9316to9333;

  true9316to9384:
    assume local4 == stack0o;
    goto block9384;

  false9316to9333:
    assume local4 != stack0o;
    goto block9333;

  block9384:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(71,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Friend.th] != null;
    assert $Heap[temp2, Friend.x] == $Heap[$Heap[temp2, Friend.th], Thing.y];
    assert $Heap[$Heap[temp2, Friend.th], Thing.f] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Friend;
    assume IsHeap($Heap);
    goto block9367;

  block9333:
    // ----- is instance
    // ----- branch
    goto true9333to9384, false9333to9350;

  true9333to9384:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block9384;

  false9333to9350:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block9350;

  block9350:
    // ----- branch
    goto block9367;

  block9367:
    // ----- nop
    // ----- branch
    goto block9231;

  block9231:
    // ----- branch
    goto block9486;

  block9486:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9486to9554, false9486to9503;

  true9486to9554:
    assume local2 == stack0o;
    goto block9554;

  false9486to9503:
    assume local2 != stack0o;
    goto block9503;

  block9554:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(72,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block9537;

  block9503:
    // ----- is instance
    // ----- branch
    goto true9503to9554, false9503to9520;

  true9503to9554:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block9554;

  false9503to9520:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block9520;

  block9520:
    // ----- branch
    goto block9537;

  block9537:
    // ----- nop
    // ----- branch
    goto block9282;

  block9282:
    // ----- return
    return;

}



procedure Thing.Q(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] != null;
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



implementation Thing.Q(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack0o: ref, temp2: ref, stack1s: struct, stack1o: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), local5: int where InRange(local5, System.Int32), stack0i: int, local6: ref where $Is(local6, Friend), local7: int where InRange(local7, System.Int32), stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block11339;

  block11339:
    goto block11543;

  block11543:
    // ----- nop
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(78,22)
    temp0 := this;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(78,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block11560;

  block11560:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(79,15)
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(79,15)
    temp2 := stack0o;
    // ----- load token  ----- VisibilityBasedInvariants.ssc(79,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(79,15)
    stack1o := TypeObject(Friend);
    // ----- local unpack  ----- VisibilityBasedInvariants.ssc(79,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: Friend && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block11577;

  block11577:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(80,9)
    assert this != null;
    local5 := $Heap[this, Thing.y];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(80,9)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(80,9)
    stack0i := local5 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(80,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Thing) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == this ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Thing.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- load field  ----- VisibilityBasedInvariants.ssc(81,9)
    assert this != null;
    local6 := $Heap[this, Thing.f];
    // ----- load field  ----- VisibilityBasedInvariants.ssc(81,9)
    assert local6 != null;
    local7 := $Heap[local6, Friend.x];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(81,9)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(81,9)
    stack0i := local7 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(81,9)
    assert local6 != null;
    assert !($Heap[local6, $inv] <: Friend) || $Heap[local6, $localinv] == System.Object;
    $Heap[local6, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local7;
    // ----- branch
    goto block11713;

  block11713:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11713to11781, false11713to11730;

  true11713to11781:
    assume local4 == stack0o;
    goto block11781;

  false11713to11730:
    assume local4 != stack0o;
    goto block11730;

  block11781:
    // ----- load token  ----- VisibilityBasedInvariants.ssc(82,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(82,7)
    stack0o := TypeObject(Friend);
    // ----- local pack  ----- VisibilityBasedInvariants.ssc(82,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert $Heap[temp2, Friend.th] != null;
    assert $Heap[temp2, Friend.x] == $Heap[$Heap[temp2, Friend.th], Thing.y];
    assert $Heap[$Heap[temp2, Friend.th], Thing.f] == temp2;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block11764;

  block11730:
    // ----- is instance
    // ----- branch
    goto true11730to11781, false11730to11747;

  true11730to11781:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block11781;

  false11730to11747:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block11747;

  block11747:
    // ----- branch
    goto block11764;

  block11764:
    // ----- nop
    // ----- branch
    goto block11628;

  block11628:
    // ----- branch
    goto block11883;

  block11883:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11883to11951, false11883to11900;

  true11883to11951:
    assume local2 == stack0o;
    goto block11951;

  false11883to11900:
    assume local2 != stack0o;
    goto block11900;

  block11951:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(83,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block11934;

  block11900:
    // ----- is instance
    // ----- branch
    goto true11900to11951, false11900to11917;

  true11900to11951:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block11951;

  false11900to11917:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block11917;

  block11917:
    // ----- branch
    goto block11934;

  block11934:
    // ----- nop
    // ----- branch
    goto block11679;

  block11679:
    // ----- return
    return;

}



procedure Thing.R(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] != null;
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



implementation Thing.R(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: ref where $Is(local3, Friend), local4: int where InRange(local4, System.Int32), stack0i: int, temp2: ref, temp3: exposeVersionType, local6: ref where $Is(local6, System.Exception), local7: int where InRange(local7, System.Int32), stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block13838;

  block13838:
    goto block14042;

  block14042:
    // ----- nop
    // ----- load field  ----- VisibilityBasedInvariants.ssc(89,13)
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(89,13)
    temp0 := stack0o;
    // ----- load token  ----- VisibilityBasedInvariants.ssc(89,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(89,13)
    stack1o := TypeObject(Friend);
    // ----- local unpack  ----- VisibilityBasedInvariants.ssc(89,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Friend && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block14059;

  block14059:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(90,7)
    assert this != null;
    local3 := $Heap[this, Thing.f];
    // ----- load field  ----- VisibilityBasedInvariants.ssc(90,7)
    assert local3 != null;
    local4 := $Heap[local3, Friend.x];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(90,7)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(90,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(90,7)
    assert local3 != null;
    assert !($Heap[local3, $inv] <: Friend) || $Heap[local3, $localinv] == System.Object;
    $Heap[local3, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(91,24)
    temp2 := this;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(91,24)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] == Thing && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $inv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local6 := null;
    goto block14076;

  block14076:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(92,9)
    assert this != null;
    local7 := $Heap[this, Thing.y];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(92,9)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(92,9)
    stack0i := local7 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(92,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Thing) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == this ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Thing.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local7;
    // ----- branch
    goto block14212;

  block14212:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14212to14280, false14212to14229;

  true14212to14280:
    assume local6 == stack0o;
    goto block14280;

  false14212to14229:
    assume local6 != stack0o;
    goto block14229;

  block14280:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(93,7)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[temp2, Thing.f] == null || $Heap[$Heap[temp2, Thing.f], Friend.th] == temp2;
    assert 0 <= $Heap[temp2, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := Thing;
    assume IsHeap($Heap);
    goto block14263;

  block14229:
    // ----- is instance
    // ----- branch
    goto true14229to14280, false14229to14246;

  true14229to14280:
    assume $As(local6, Microsoft.Contracts.ICheckedException) != null;
    goto block14280;

  false14229to14246:
    assume $As(local6, Microsoft.Contracts.ICheckedException) == null;
    goto block14246;

  block14246:
    // ----- branch
    goto block14263;

  block14263:
    // ----- nop
    // ----- branch
    goto block14127;

  block14127:
    // ----- branch
    goto block14382;

  block14382:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true14382to14450, false14382to14399;

  true14382to14450:
    assume local2 == stack0o;
    goto block14450;

  false14382to14399:
    assume local2 != stack0o;
    goto block14399;

  block14450:
    // ----- load token  ----- VisibilityBasedInvariants.ssc(94,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(94,5)
    stack0o := TypeObject(Friend);
    // ----- local pack  ----- VisibilityBasedInvariants.ssc(94,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[temp0, Friend.th] != null;
    assert $Heap[temp0, Friend.x] == $Heap[$Heap[temp0, Friend.th], Thing.y];
    assert $Heap[$Heap[temp0, Friend.th], Thing.f] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block14433;

  block14399:
    // ----- is instance
    // ----- branch
    goto true14399to14450, false14399to14416;

  true14399to14450:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block14450;

  false14399to14416:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block14416;

  block14416:
    // ----- branch
    goto block14433;

  block14433:
    // ----- nop
    // ----- branch
    goto block14178;

  block14178:
    // ----- return
    return;

}



procedure Thing.S(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] != null;
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



implementation Thing.S(this: ref)
{
  var stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: ref where $Is(local3, Friend), local4: int where InRange(local4, System.Int32), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block16099;

  block16099:
    goto block16303;

  block16303:
    // ----- nop
    // ----- load field  ----- VisibilityBasedInvariants.ssc(100,13)
    assert this != null;
    stack0o := $Heap[this, Thing.f];
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(100,13)
    temp0 := stack0o;
    // ----- load token  ----- VisibilityBasedInvariants.ssc(100,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(100,13)
    stack1o := TypeObject(Friend);
    // ----- local unpack  ----- VisibilityBasedInvariants.ssc(100,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: Friend && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block16320;

  block16320:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(101,7)
    assert this != null;
    local3 := $Heap[this, Thing.f];
    // ----- load field  ----- VisibilityBasedInvariants.ssc(101,7)
    assert local3 != null;
    local4 := $Heap[local3, Friend.x];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(101,7)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(101,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(101,7)
    assert local3 != null;
    assert !($Heap[local3, $inv] <: Friend) || $Heap[local3, $localinv] == System.Object;
    $Heap[local3, Friend.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block16405;

  block16405:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true16405to16473, false16405to16422;

  true16405to16473:
    assume local2 == stack0o;
    goto block16473;

  false16405to16422:
    assume local2 != stack0o;
    goto block16422;

  block16473:
    // ----- load token  ----- VisibilityBasedInvariants.ssc(102,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, Friend);
    // ----- statically resolved GetTypeFromHandle call  ----- VisibilityBasedInvariants.ssc(102,5)
    stack0o := TypeObject(Friend);
    // ----- local pack  ----- VisibilityBasedInvariants.ssc(102,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[temp0, Friend.th] != null;
    assert $Heap[temp0, Friend.x] == $Heap[$Heap[temp0, Friend.th], Thing.y];
    assert $Heap[$Heap[temp0, Friend.th], Thing.f] == temp0;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Friend ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block16456;

  block16422:
    // ----- is instance
    // ----- branch
    goto true16422to16473, false16422to16439;

  true16422to16473:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block16473;

  false16422to16439:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block16439;

  block16439:
    // ----- branch
    goto block16456;

  block16456:
    // ----- nop
    // ----- branch
    goto block16371;

  block16371:
    // ----- return
    return;

}



procedure Thing.T(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] != null;
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



implementation Thing.T(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block17663;

  block17663:
    goto block17867;

  block17867:
    // ----- nop
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(108,22)
    temp0 := this;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(108,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block17884;

  block17884:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(109,7)
    assert this != null;
    local3 := $Heap[this, Thing.y];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(109,7)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(109,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(109,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Thing) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == this ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Thing.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block17969;

  block17969:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true17969to18037, false17969to17986;

  true17969to18037:
    assume local2 == stack0o;
    goto block18037;

  false17969to17986:
    assume local2 != stack0o;
    goto block17986;

  block18037:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(110,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block18020;

  block17986:
    // ----- is instance
    // ----- branch
    goto true17986to18037, false17986to18003;

  true17986to18037:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block18037;

  false17986to18003:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block18003;

  block18003:
    // ----- branch
    goto block18020;

  block18020:
    // ----- nop
    // ----- branch
    goto block17935;

  block17935:
    // ----- return
    return;

}



procedure Thing.U(this: ref);
  // user-declared preconditions
  requires $Heap[this, Thing.f] == null;
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



implementation Thing.U(this: ref)
{
  var temp0: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Thing);
    assume $Heap[this, $allocated] == true;
    goto block19091;

  block19091:
    goto block19295;

  block19295:
    // ----- nop
    // ----- FrameGuard processing  ----- VisibilityBasedInvariants.ssc(116,22)
    temp0 := this;
    // ----- classic unpack  ----- VisibilityBasedInvariants.ssc(116,22)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] == Thing && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $inv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block19312;

  block19312:
    // ----- load field  ----- VisibilityBasedInvariants.ssc(117,7)
    assert this != null;
    local3 := $Heap[this, Thing.y];
    // ----- load constant 1  ----- VisibilityBasedInvariants.ssc(117,7)
    stack0i := 1;
    // ----- binary operator  ----- VisibilityBasedInvariants.ssc(117,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- VisibilityBasedInvariants.ssc(117,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Thing) || $Heap[this, $localinv] == System.Object;
    assert (forall $o: ref :: $o != null && $Heap[$o, $allocated] == true && $typeof($o) <: Friend && $Heap[$o, Friend.th] == this ==> !($Heap[$o, $inv] <: Friend) || $Heap[$o, $localinv] == System.Object);
    $Heap[this, Thing.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block19397;

  block19397:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true19397to19465, false19397to19414;

  true19397to19465:
    assume local2 == stack0o;
    goto block19465;

  false19397to19414:
    assume local2 != stack0o;
    goto block19414;

  block19465:
    // ----- classic pack  ----- VisibilityBasedInvariants.ssc(118,5)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[temp0, Thing.f] == null || $Heap[$Heap[temp0, Thing.f], Friend.th] == temp0;
    assert 0 <= $Heap[temp0, Thing.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == Thing ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := Thing;
    assume IsHeap($Heap);
    goto block19448;

  block19414:
    // ----- is instance
    // ----- branch
    goto true19414to19465, false19414to19431;

  true19414to19465:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block19465;

  false19414to19431:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block19431;

  block19431:
    // ----- branch
    goto block19448;

  block19448:
    // ----- nop
    // ----- branch
    goto block19363;

  block19363:
    // ----- return
    return;

}



procedure Thing..cctor();
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



implementation Thing..cctor()
{

  entry:
    goto block20179;

  block20179:
    goto block20230;

  block20230:
    // ----- nop
    // ----- return
    return;

}


