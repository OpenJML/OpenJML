// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo Change773

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

const System.Boolean: name;

const Test2: name;

const Test1: name;

axiom Test1 <: Test1;

axiom $BaseClass(Test1) == System.Object;

axiom Test1 <: $BaseClass(Test1) && AsDirectSubClass(Test1, $BaseClass(Test1)) == Test1;

axiom !$IsImmutable(Test1) && $AsMutable(Test1) == Test1;

axiom (forall $U: name :: { $U <: Test1 } $U <: Test1 ==> $U == Test1);

procedure Test1.Foo$System.Int32.array$notnull$System.Object$notnull(xs$in: ref where $IsNotNull(xs$in, ValueArray(System.Int32, 1)), o$in: ref where $IsNotNull(o$in, System.Object));
  free requires $Heap[xs$in, $allocated] == true;
  free requires $Heap[o$in, $allocated] == true;
  requires ($Heap[xs$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[xs$in, $ownerRef], $inv] <: $Heap[xs$in, $ownerFrame]) || $Heap[$Heap[xs$in, $ownerRef], $localinv] == $BaseClass($Heap[xs$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[xs$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[xs$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame]) || $Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Test1.Foo$System.Int32.array$notnull$System.Object$notnull(xs$in: ref, o$in: ref)
{
  var xs: ref where $IsNotNull(xs, ValueArray(System.Int32, 1)), o: ref where $IsNotNull(o, System.Object), stack0b: bool, b: bool where true, stack0o: ref, stack1i: int, i: int where InRange(i, System.Int32);

  entry:
    xs := xs$in;
    o := o$in;
    goto block2618;

  block2618:
    goto block2635;

  block2635:
    // ----- binary operator  ----- Change773.ssc(5,18)
    // ----- branch  ----- Change773.ssc(5,18)
    goto true2635to2669, false2635to2652;

  true2635to2669:
    assume xs == o;
    goto block2669;

  false2635to2652:
    assume xs != o;
    goto block2652;

  block2669:
    goto block2686;

  block2652:
    // ----- load constant False  ----- Change773.ssc(5,18)
    stack0b := false;
    // ----- branch  ----- Change773.ssc(5,18)
    goto block2703;

  block2686:
    // ----- load constant True  ----- Change773.ssc(5,18)
    stack0b := true;
    goto block2703;

  block2703:
    goto block2720;

  block2720:
    // ----- copy  ----- Change773.ssc(5,9)
    b := stack0b;
    goto block2737;

  block2737:
    // ----- copy  ----- Change773.ssc(6,17)
    stack0o := xs;
    // ----- load constant 1  ----- Change773.ssc(6,20)
    stack1i := 1;
    // ----- load element  ----- Change773.ssc(6,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    i := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    goto block2754;

  block2754:
    goto block2771;

  block2771:
    // ----- return  ----- Change773.ssc(7,5)
    return;

}



axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Test1..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Test1 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Test1 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Test1..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Test1);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block3026;

  block3026:
    goto block3043;

  block3043:
    goto block3060;

  block3060:
    // ----- call  ----- Change773.ssc(1,7)
    assert this != null;
    call System.Object..ctor(this);
    goto block3077;

  block3077:
    goto block3094;

  block3094:
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Test1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Test1;
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



axiom Test2 <: Test2;

axiom $BaseClass(Test2) == System.Object;

axiom Test2 <: $BaseClass(Test2) && AsDirectSubClass(Test2, $BaseClass(Test2)) == Test2;

axiom !$IsImmutable(Test2) && $AsMutable(Test2) == Test2;

axiom (forall $U: name :: { $U <: Test2 } $U <: Test2 ==> $U == Test2);

procedure Test2.Foo();
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



implementation Test2.Foo()
{
  var stack0i: int, xs: ref where $Is(xs, ValueArray(System.Int32, 1)), stack0o: ref, stack1i: int, i: int where InRange(i, System.Int32);

  entry:
    goto block3281;

  block3281:
    goto block3298;

  block3298:
    // ----- load constant 4  ----- Change773.ssc(14,28)
    stack0i := 4;
    // ----- new array  ----- Change773.ssc(14,9)
    assert 0 <= stack0i;
    havoc xs;
    assume $Heap[xs, $allocated] == false && $Length(xs) == stack0i;
    assume $IsNotNull(xs, ValueArray(System.Int32, 1));
    assume $Heap[xs, $ownerRef] == xs && $Heap[xs, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[xs, $inv] == ValueArray(System.Int32, 1) && $Heap[xs, $localinv] == ValueArray(System.Int32, 1) && ($Heap[xs, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[xs, $ownerRef], $inv] <: $Heap[xs, $ownerFrame]) || $Heap[$Heap[xs, $ownerRef], $localinv] == $BaseClass($Heap[xs, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[xs, $elements], $i),int) == 0);
    $Heap[xs, $allocated] := true;
    assume IsHeap($Heap);
    goto block3315;

  block3315:
    // ----- copy  ----- Change773.ssc(15,17)
    stack0o := xs;
    // ----- load constant 1  ----- Change773.ssc(15,20)
    stack1i := 1;
    // ----- load element  ----- Change773.ssc(15,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    i := cast(ValueArrayGet($Heap[stack0o, $elements], stack1i),int);
    goto block3332;

  block3332:
    goto block3349;

  block3349:
    // ----- return  ----- Change773.ssc(16,5)
    return;

}



procedure Test2..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Test2 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Test2 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Test2..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Test2);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block3519;

  block3519:
    goto block3536;

  block3536:
    goto block3553;

  block3553:
    // ----- call  ----- Change773.ssc(10,7)
    assert this != null;
    call System.Object..ctor(this);
    goto block3570;

  block3570:
    goto block3587;

  block3587:
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Test2 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Test2;
    assume IsHeap($Heap);
    return;

}


