// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify /infer:eh loopinv1.dll

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

const LoopInv1.field: <ref>name;

const F.X: <int>name;

const System.Reflection.ICustomAttributeProvider: name;

const System.IConvertible: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.IComparable: name;

const System.Reflection.IReflect: name;

const System.IComparable`1...System.String: name;

const System.Collections.IEnumerable: name;

const System.Runtime.InteropServices._Type: name;

const System.Reflection.MemberInfo: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const F: name;

const System.IEquatable`1...System.String: name;

const System.ICloneable: name;

const LoopInv1: name;

axiom !IsStaticField(F.X);

axiom IsDirectlyModifiableField(F.X);

axiom DeclType(F.X) == F;

axiom AsRangeField(F.X, System.Int32) == F.X;

axiom !IsStaticField(LoopInv1.field);

axiom IsDirectlyModifiableField(LoopInv1.field);

axiom DeclType(LoopInv1.field) == LoopInv1;

axiom AsRefField(LoopInv1.field, F) == LoopInv1.field;

axiom F <: F;

axiom $BaseClass(F) == System.Object;

axiom F <: $BaseClass(F) && AsDirectSubClass(F, $BaseClass(F)) == F;

axiom !$IsImmutable(F) && $AsMutable(F) == F;

axiom (forall $U: name :: { $U <: F } $U <: F ==> $U == F);

procedure F.M(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(F <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation F.M(this: ref)
{
  var local0: ref where $Is(local0, F), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0i: int;

  entry:
    assume $IsNotNull(this, F);
    assume $Heap[this, $allocated] == true;
    goto block1581;

  block1581:
    goto block1649;

  block1649:
    // ----- copy  ----- loopinv1.ssc(9,12)
    local0 := this;
    // ----- copy  ----- loopinv1.ssc(9,12)
    stack0o := local0;
    // ----- load token  ----- loopinv1.ssc(9,12)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(9,12)
    stack1o := TypeObject(F);
    // ----- local unpack  ----- loopinv1.ssc(9,12)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: F && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block1666;

  block1666:
    // ----- load constant 4  ----- loopinv1.ssc(9,20)
    stack0i := 4;
    // ----- store field  ----- loopinv1.ssc(9,20)
    assert this != null;
    assert !($Heap[this, $inv] <: F) || $Heap[this, $localinv] == System.Object;
    $Heap[this, F.X] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block1717;

  block1717:
    // ----- copy  ----- loopinv1.ssc(9,27)
    stack0o := local0;
    // ----- load token  ----- loopinv1.ssc(9,27)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(9,27)
    stack1o := TypeObject(F);
    // ----- local pack  ----- loopinv1.ssc(9,27)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == F ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block1683;

  block1683:
    // ----- return  ----- loopinv1.ssc(9,29)
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

procedure F.NoOp(this: ref);
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  free ensures $Heap == old($Heap);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation F.NoOp(this: ref)
{

  entry:
    assume $IsNotNull(this, F);
    assume $Heap[this, $allocated] == true;
    goto block2108;

  block2108:
    goto block2125;

  block2125:
    // ----- return  ----- loopinv1.ssc(12,24)
    return;

}



procedure F..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == F && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(F <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation F..ctor(this: ref)
{
  var stack0i: int;

  entry:
    assume $IsNotNull(this, F);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, F.X] == 0;
    goto block2278;

  block2278:
    goto block2295;

  block2295:
    // ----- load constant 0  ----- loopinv1.ssc(6,3)
    stack0i := 0;
    // ----- store field  ----- loopinv1.ssc(6,3)
    assert this != null;
    assert !($Heap[this, $inv] <: F) || $Heap[this, $localinv] == System.Object;
    $Heap[this, F.X] := stack0i;
    assume IsHeap($Heap);
    // ----- call  ----- loopinv1.ssc(4,21)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == F ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := F;
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



axiom LoopInv1 <: LoopInv1;

axiom $BaseClass(LoopInv1) == System.Object;

axiom LoopInv1 <: $BaseClass(LoopInv1) && AsDirectSubClass(LoopInv1, $BaseClass(LoopInv1)) == LoopInv1;

axiom !$IsImmutable(LoopInv1) && $AsMutable(LoopInv1) == LoopInv1;

axiom (forall $U: name :: { $U <: LoopInv1 } $U <: LoopInv1 ==> $U == LoopInv1);

procedure LoopInv1.Test0a$F$notnull(this: ref, other$in: ref where $IsNotNull(other$in, F));
  free requires $Heap[other$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && $Heap[other$in, $inv] == F && $Heap[other$in, $localinv] == $typeof(other$in);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[other$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[other$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, LoopInv1.field] != null;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != this || !(LoopInv1 <: DeclType($f))) && ($o != other$in || !($typeof(other$in) <: DeclType($f)))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation LoopInv1.Test0a$F$notnull(this: ref, other$in: ref)
{
  var other: ref where $IsNotNull(other, F), local1: ref where $Is(local1, LoopInv1), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack50000o: ref, i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local4: int where InRange(local4, System.Int32), $Heap$block3111$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, LoopInv1);
    assume $Heap[this, $allocated] == true;
    other := other$in;
    goto block2907;

  block2907:
    goto block3060;

  block3060:
    // ----- nop
    // ----- copy  ----- loopinv1.ssc(24,15)
    local1 := this;
    // ----- copy  ----- loopinv1.ssc(24,15)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(24,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(24,15)
    stack1o := TypeObject(LoopInv1);
    // ----- local unpack  ----- loopinv1.ssc(24,15)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: LoopInv1 && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block3077;

  block3077:
    // ----- new object  ----- loopinv1.ssc(26,9)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == F;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- loopinv1.ssc(26,9)
    assert stack50000o != null;
    call F..ctor(stack50000o);
    // ----- copy  ----- loopinv1.ssc(26,9)
    stack0o := stack50000o;
    // ----- store field  ----- loopinv1.ssc(26,9)
    assert this != null;
    assert !($Heap[this, $inv] <: LoopInv1) || $Heap[this, $localinv] == System.Object;
    $Heap[this, LoopInv1.field] := stack0o;
    assume IsHeap($Heap);
    // ----- branch
    goto block3383;

  block3383:
    // ----- copy  ----- loopinv1.ssc(27,7)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(27,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(27,7)
    stack1o := TypeObject(LoopInv1);
    // ----- local pack  ----- loopinv1.ssc(27,7)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == LoopInv1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block3094;

  block3094:
    // ----- load constant 0  ----- loopinv1.ssc(29,12)
    i := 0;
    goto block3111$LoopPreheader;

  block3111:
    // ----- default loop invariant: allocation and ownership are stable  ----- loopinv1.ssc(32,25)
    assume (forall $o: ref :: $Heap$block3111$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block3111$LoopPreheader[$ot, $allocated] == true && $Heap$block3111$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block3111$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block3111$LoopPreheader[$ot, $ownerFrame]) && $Heap$block3111$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- loopinv1.ssc(32,25)
    assume (forall $o: ref :: ($Heap$block3111$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block3111$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block3111$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block3111$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- loopinv1.ssc(32,25)
    assert (forall $o: ref :: $o != null && $Heap$block3111$LoopPreheader[$o, $allocated] == true ==> $Heap$block3111$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block3111$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- loopinv1.ssc(32,25)
    assert ($Heap[other, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other, $ownerRef], $inv] <: $Heap[other, $ownerFrame]) || $Heap[$Heap[other, $ownerRef], $localinv] == $BaseClass($Heap[other, $ownerFrame])) && $Heap[other, $inv] == F && $Heap[other, $localinv] == $typeof(other);
    // ----- serialized LoopInvariant  ----- loopinv1.ssc(33,24)
    assert ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == LoopInv1 && $Heap[this, $localinv] == $typeof(this);
    goto block3230;

  block3230:
    // ----- nop
    // ----- load constant 10  ----- loopinv1.ssc(29,23)
    stack0i := 10;
    // ----- binary operator  ----- loopinv1.ssc(29,23)
    // ----- branch  ----- loopinv1.ssc(29,23)
    goto true3230to3264, false3230to3247;

  true3230to3264:
    assume i >= stack0i;
    goto block3264;

  false3230to3247:
    assume i < stack0i;
    goto block3247;

  block3264:
    goto block3349;

  block3247:
    // ----- call  ----- loopinv1.ssc(35,9)
    assert other != null;
    call F.M(other);
    // ----- copy  ----- loopinv1.ssc(29,31)
    local4 := i;
    // ----- load constant 1  ----- loopinv1.ssc(29,31)
    stack0i := 1;
    // ----- binary operator  ----- loopinv1.ssc(29,31)
    stack0i := local4 + stack0i;
    // ----- copy  ----- loopinv1.ssc(29,31)
    i := stack0i;
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block3111;

  block3349:
    // ----- nop
    // ----- return
    return;

  block3111$LoopPreheader:
    $Heap$block3111$LoopPreheader := $Heap;
    goto block3111;

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

procedure LoopInv1.Test0b$F$notnull(this: ref, other$in: ref where $IsNotNull(other$in, F));
  free requires $Heap[other$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && $Heap[other$in, $inv] == F && $Heap[other$in, $localinv] == $typeof(other$in);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[other$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[other$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, LoopInv1.field] != null;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != this || !(LoopInv1 <: DeclType($f))) && ($o != other$in || !($typeof(other$in) <: DeclType($f)))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation LoopInv1.Test0b$F$notnull(this: ref, other$in: ref)
{
  var other: ref where $IsNotNull(other, F), local1: ref where $Is(local1, LoopInv1), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack50000o: ref, save: ref where $Is(save, F), i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local5: int where InRange(local5, System.Int32), $Heap$block4777$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, LoopInv1);
    assume $Heap[this, $allocated] == true;
    other := other$in;
    goto block4573;

  block4573:
    goto block4726;

  block4726:
    // ----- nop
    // ----- copy  ----- loopinv1.ssc(44,15)
    local1 := this;
    // ----- copy  ----- loopinv1.ssc(44,15)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(44,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(44,15)
    stack1o := TypeObject(LoopInv1);
    // ----- local unpack  ----- loopinv1.ssc(44,15)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: LoopInv1 && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block4743;

  block4743:
    // ----- new object  ----- loopinv1.ssc(46,9)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == F;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- loopinv1.ssc(46,9)
    assert stack50000o != null;
    call F..ctor(stack50000o);
    // ----- copy  ----- loopinv1.ssc(46,9)
    stack0o := stack50000o;
    // ----- store field  ----- loopinv1.ssc(46,9)
    assert this != null;
    assert !($Heap[this, $inv] <: LoopInv1) || $Heap[this, $localinv] == System.Object;
    $Heap[this, LoopInv1.field] := stack0o;
    assume IsHeap($Heap);
    // ----- branch
    goto block5015;

  block5015:
    // ----- copy  ----- loopinv1.ssc(47,7)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(47,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(47,7)
    stack1o := TypeObject(LoopInv1);
    // ----- local pack  ----- loopinv1.ssc(47,7)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == LoopInv1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block4760;

  block4760:
    // ----- load field  ----- loopinv1.ssc(49,7)
    assert this != null;
    save := $Heap[this, LoopInv1.field];
    // ----- call  ----- loopinv1.ssc(50,7)
    assert save != null;
    call F.NoOp(save);
    // ----- load constant 0  ----- loopinv1.ssc(51,12)
    i := 0;
    goto block4777$LoopPreheader;

  block4777:
    // ----- default loop invariant: allocation and ownership are stable  ----- loopinv1.ssc(54,25)
    assume (forall $o: ref :: $Heap$block4777$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block4777$LoopPreheader[$ot, $allocated] == true && $Heap$block4777$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block4777$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block4777$LoopPreheader[$ot, $ownerFrame]) && $Heap$block4777$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- loopinv1.ssc(54,25)
    assume (forall $o: ref :: ($Heap$block4777$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block4777$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block4777$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block4777$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- loopinv1.ssc(54,25)
    assert (forall $o: ref :: $o != null && $Heap$block4777$LoopPreheader[$o, $allocated] == true ==> $Heap$block4777$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block4777$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- loopinv1.ssc(54,25)
    assert ($Heap[other, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other, $ownerRef], $inv] <: $Heap[other, $ownerFrame]) || $Heap[$Heap[other, $ownerRef], $localinv] == $BaseClass($Heap[other, $ownerFrame])) && $Heap[other, $inv] == F && $Heap[other, $localinv] == $typeof(other);
    goto block4862;

  block4862:
    // ----- nop
    // ----- load constant 10  ----- loopinv1.ssc(51,23)
    stack0i := 10;
    // ----- binary operator  ----- loopinv1.ssc(51,23)
    // ----- branch  ----- loopinv1.ssc(51,23)
    goto true4862to4896, false4862to4879;

  true4862to4896:
    assume i >= stack0i;
    goto block4896;

  false4862to4879:
    assume i < stack0i;
    goto block4879;

  block4896:
    goto block4981;

  block4879:
    // ----- call  ----- loopinv1.ssc(56,9)
    assert other != null;
    call F.M(other);
    // ----- copy  ----- loopinv1.ssc(51,31)
    local5 := i;
    // ----- load constant 1  ----- loopinv1.ssc(51,31)
    stack0i := 1;
    // ----- binary operator  ----- loopinv1.ssc(51,31)
    stack0i := local5 + stack0i;
    // ----- copy  ----- loopinv1.ssc(51,31)
    i := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block4777;

  block4981:
    // ----- nop
    // ----- return
    return;

  block4777$LoopPreheader:
    $Heap$block4777$LoopPreheader := $Heap;
    goto block4777;

}



procedure LoopInv1.Test1a$F$notnull(this: ref, other$in: ref where $IsNotNull(other$in, F));
  free requires $Heap[other$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && $Heap[other$in, $inv] == F && $Heap[other$in, $localinv] == $typeof(other$in);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[other$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[other$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, LoopInv1.field] != null;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(($o != this || !(LoopInv1 <: DeclType($f))) && ($o != other$in || !($typeof(other$in) <: DeclType($f)))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation LoopInv1.Test1a$F$notnull(this: ref, other$in: ref)
{
  var other: ref where $IsNotNull(other, F), local1: ref where $Is(local1, LoopInv1), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack50000o: ref, i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local4: ref where $Is(local4, F), temp1: exposeVersionType, local5: int where InRange(local5, System.Int32), $Heap$block6477$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, LoopInv1);
    assume $Heap[this, $allocated] == true;
    other := other$in;
    goto block6273;

  block6273:
    goto block6426;

  block6426:
    // ----- nop
    // ----- copy  ----- loopinv1.ssc(66,15)
    local1 := this;
    // ----- copy  ----- loopinv1.ssc(66,15)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(66,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(66,15)
    stack1o := TypeObject(LoopInv1);
    // ----- local unpack  ----- loopinv1.ssc(66,15)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: LoopInv1 && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block6443;

  block6443:
    // ----- new object  ----- loopinv1.ssc(68,9)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == F;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- loopinv1.ssc(68,9)
    assert stack50000o != null;
    call F..ctor(stack50000o);
    // ----- copy  ----- loopinv1.ssc(68,9)
    stack0o := stack50000o;
    // ----- store field  ----- loopinv1.ssc(68,9)
    assert this != null;
    assert !($Heap[this, $inv] <: LoopInv1) || $Heap[this, $localinv] == System.Object;
    $Heap[this, LoopInv1.field] := stack0o;
    assume IsHeap($Heap);
    // ----- branch
    goto block6749;

  block6749:
    // ----- copy  ----- loopinv1.ssc(69,7)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(69,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(69,7)
    stack1o := TypeObject(LoopInv1);
    // ----- local pack  ----- loopinv1.ssc(69,7)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == LoopInv1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block6460;

  block6460:
    // ----- load constant 0  ----- loopinv1.ssc(71,12)
    i := 0;
    goto block6477$LoopPreheader;

  block6477:
    // ----- default loop invariant: allocation and ownership are stable  ----- loopinv1.ssc(74,25)
    assume (forall $o: ref :: $Heap$block6477$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block6477$LoopPreheader[$ot, $allocated] == true && $Heap$block6477$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block6477$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block6477$LoopPreheader[$ot, $ownerFrame]) && $Heap$block6477$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- loopinv1.ssc(74,25)
    assume (forall $o: ref :: ($Heap$block6477$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block6477$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block6477$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block6477$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- loopinv1.ssc(74,25)
    assert (forall $o: ref :: $o != null && $Heap$block6477$LoopPreheader[$o, $allocated] == true ==> $Heap$block6477$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block6477$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- loopinv1.ssc(74,25)
    assert ($Heap[other, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other, $ownerRef], $inv] <: $Heap[other, $ownerFrame]) || $Heap[$Heap[other, $ownerRef], $localinv] == $BaseClass($Heap[other, $ownerFrame])) && $Heap[other, $inv] == F && $Heap[other, $localinv] == $typeof(other);
    goto block6562;

  block6562:
    // ----- nop
    // ----- load constant 10  ----- loopinv1.ssc(71,23)
    stack0i := 10;
    // ----- binary operator  ----- loopinv1.ssc(71,23)
    // ----- branch  ----- loopinv1.ssc(71,23)
    goto true6562to6630, false6562to6579;

  true6562to6630:
    assume i >= stack0i;
    goto block6630;

  false6562to6579:
    assume i < stack0i;
    goto block6579;

  block6630:
    goto block6715;

  block6579:
    // ----- copy  ----- loopinv1.ssc(76,17)
    local4 := other;
    // ----- copy  ----- loopinv1.ssc(76,17)
    stack0o := local4;
    // ----- load token  ----- loopinv1.ssc(76,17)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(76,17)
    stack1o := TypeObject(F);
    // ----- local unpack  ----- loopinv1.ssc(76,17)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: F && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp1;
    $Heap[stack0o, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    goto block6596;

  block6715:
    // ----- nop
    // ----- return
    return;

  block6596:
    // ----- load constant 4  ----- loopinv1.ssc(76,26)
    stack0i := 4;
    // ----- store field  ----- loopinv1.ssc(76,26)
    assert other != null;
    assert !($Heap[other, $inv] <: F) || $Heap[other, $localinv] == System.Object;
    $Heap[other, F.X] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block6766;

  block6766:
    // ----- copy  ----- loopinv1.ssc(76,39)
    stack0o := local4;
    // ----- load token  ----- loopinv1.ssc(76,39)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(76,39)
    stack1o := TypeObject(F);
    // ----- local pack  ----- loopinv1.ssc(76,39)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == F ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block6613;

  block6613:
    // ----- copy  ----- loopinv1.ssc(71,31)
    local5 := i;
    // ----- load constant 1  ----- loopinv1.ssc(71,31)
    stack0i := 1;
    // ----- binary operator  ----- loopinv1.ssc(71,31)
    stack0i := local5 + stack0i;
    // ----- copy  ----- loopinv1.ssc(71,31)
    i := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block6477;

  block6477$LoopPreheader:
    $Heap$block6477$LoopPreheader := $Heap;
    goto block6477;

}



procedure LoopInv1.Test1b$F$notnull(this: ref, other$in: ref where $IsNotNull(other$in, F));
  free requires $Heap[other$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && $Heap[other$in, $inv] == F && $Heap[other$in, $localinv] == $typeof(other$in);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[other$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other$in, $ownerRef], $inv] <: $Heap[other$in, $ownerFrame]) || $Heap[$Heap[other$in, $ownerRef], $localinv] == $BaseClass($Heap[other$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[other$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[other$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[this, LoopInv1.field] != null;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(LoopInv1 <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation LoopInv1.Test1b$F$notnull(this: ref, other$in: ref)
{
  var other: ref where $IsNotNull(other, F), local1: ref where $Is(local1, LoopInv1), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack50000o: ref, save: ref where $Is(save, F), i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local5: ref where $Is(local5, F), temp1: exposeVersionType, local6: int where InRange(local6, System.Int32), $Heap$block8483$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, LoopInv1);
    assume $Heap[this, $allocated] == true;
    other := other$in;
    goto block8279;

  block8279:
    goto block8432;

  block8432:
    // ----- nop
    // ----- copy  ----- loopinv1.ssc(85,15)
    local1 := this;
    // ----- copy  ----- loopinv1.ssc(85,15)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(85,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(85,15)
    stack1o := TypeObject(LoopInv1);
    // ----- local unpack  ----- loopinv1.ssc(85,15)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: LoopInv1 && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block8449;

  block8449:
    // ----- new object  ----- loopinv1.ssc(87,9)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == F;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- loopinv1.ssc(87,9)
    assert stack50000o != null;
    call F..ctor(stack50000o);
    // ----- copy  ----- loopinv1.ssc(87,9)
    stack0o := stack50000o;
    // ----- store field  ----- loopinv1.ssc(87,9)
    assert this != null;
    assert !($Heap[this, $inv] <: LoopInv1) || $Heap[this, $localinv] == System.Object;
    $Heap[this, LoopInv1.field] := stack0o;
    assume IsHeap($Heap);
    // ----- branch
    goto block8755;

  block8755:
    // ----- copy  ----- loopinv1.ssc(88,7)
    stack0o := local1;
    // ----- load token  ----- loopinv1.ssc(88,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, LoopInv1);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(88,7)
    stack1o := TypeObject(LoopInv1);
    // ----- local pack  ----- loopinv1.ssc(88,7)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == LoopInv1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block8466;

  block8466:
    // ----- load field  ----- loopinv1.ssc(90,7)
    assert this != null;
    save := $Heap[this, LoopInv1.field];
    // ----- call  ----- loopinv1.ssc(91,7)
    assert save != null;
    call F.NoOp(save);
    // ----- load constant 0  ----- loopinv1.ssc(92,12)
    i := 0;
    goto block8483$LoopPreheader;

  block8483:
    // ----- default loop invariant: allocation and ownership are stable  ----- loopinv1.ssc(95,25)
    assume (forall $o: ref :: $Heap$block8483$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block8483$LoopPreheader[$ot, $allocated] == true && $Heap$block8483$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block8483$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block8483$LoopPreheader[$ot, $ownerFrame]) && $Heap$block8483$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- loopinv1.ssc(95,25)
    assume (forall $o: ref :: ($Heap$block8483$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block8483$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block8483$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block8483$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- loopinv1.ssc(95,25)
    assert (forall $o: ref :: $o != null && $Heap$block8483$LoopPreheader[$o, $allocated] == true ==> $Heap$block8483$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block8483$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- loopinv1.ssc(95,25)
    assert ($Heap[other, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[other, $ownerRef], $inv] <: $Heap[other, $ownerFrame]) || $Heap[$Heap[other, $ownerRef], $localinv] == $BaseClass($Heap[other, $ownerFrame])) && $Heap[other, $inv] == F && $Heap[other, $localinv] == $typeof(other);
    goto block8568;

  block8568:
    // ----- nop
    // ----- load constant 10  ----- loopinv1.ssc(92,23)
    stack0i := 10;
    // ----- binary operator  ----- loopinv1.ssc(92,23)
    // ----- branch  ----- loopinv1.ssc(92,23)
    goto true8568to8636, false8568to8585;

  true8568to8636:
    assume i >= stack0i;
    goto block8636;

  false8568to8585:
    assume i < stack0i;
    goto block8585;

  block8636:
    goto block8721;

  block8585:
    // ----- copy  ----- loopinv1.ssc(97,17)
    local5 := other;
    // ----- copy  ----- loopinv1.ssc(97,17)
    stack0o := local5;
    // ----- load token  ----- loopinv1.ssc(97,17)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(97,17)
    stack1o := TypeObject(F);
    // ----- local unpack  ----- loopinv1.ssc(97,17)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: F && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp1;
    $Heap[stack0o, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    goto block8602;

  block8721:
    // ----- nop
    // ----- return
    return;

  block8602:
    // ----- load constant 4  ----- loopinv1.ssc(97,26)
    stack0i := 4;
    // ----- store field  ----- loopinv1.ssc(97,26)
    assert other != null;
    assert !($Heap[other, $inv] <: F) || $Heap[other, $localinv] == System.Object;
    $Heap[other, F.X] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block8772;

  block8772:
    // ----- copy  ----- loopinv1.ssc(97,39)
    stack0o := local5;
    // ----- load token  ----- loopinv1.ssc(97,39)
    havoc stack1s;
    assume $IsTokenForType(stack1s, F);
    // ----- statically resolved GetTypeFromHandle call  ----- loopinv1.ssc(97,39)
    stack1o := TypeObject(F);
    // ----- local pack  ----- loopinv1.ssc(97,39)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == F ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block8619;

  block8619:
    // ----- copy  ----- loopinv1.ssc(92,31)
    local6 := i;
    // ----- load constant 1  ----- loopinv1.ssc(92,31)
    stack0i := 1;
    // ----- binary operator  ----- loopinv1.ssc(92,31)
    stack0i := local6 + stack0i;
    // ----- copy  ----- loopinv1.ssc(92,31)
    i := stack0i;
    // ----- copy
    stack0i := local6;
    // ----- branch
    goto block8483;

  block8483$LoopPreheader:
    $Heap$block8483$LoopPreheader := $Heap;
    goto block8483;

}



procedure LoopInv1..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == LoopInv1 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(LoopInv1 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation LoopInv1..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, LoopInv1);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, LoopInv1.field] == null;
    goto block9877;

  block9877:
    goto block9894;

  block9894:
    // ----- call  ----- loopinv1.ssc(15,21)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == LoopInv1 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := LoopInv1;
    assume IsHeap($Heap);
    return;

}


