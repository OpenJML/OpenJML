// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify AssignToNonInvariantField.dll

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

const AnotherClient.r: <ref>name;

const ClientClass.r: <ref>name;

const AssignToNonInvariantField.y: <int>name;

const RepClass.X: <int>name;

const T.c0: <int>name;

const T.b: <int>name;

const RepClass.Z: <int>name;

const T.e: <int>name;

const RepClass.Y: <int>name;

const T.d: <int>name;

const T.a: <int>name;

const InternalClass.X: <int>name;

const T.c1: <int>name;

const AssignToNonInvariantField.x: <int>name;

const ClientClass: name;

const Microsoft.Contracts.ICheckedException: name;

const InternalClass: name;

const T: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.IComparable`1...System.String: name;

const System.IEquatable`1...System.String: name;

const System.IConvertible: name;

const System.Runtime.InteropServices._Exception: name;

const System.Runtime.Serialization.ISerializable: name;

const System.ICloneable: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Runtime.InteropServices._Type: name;

const AnotherClient: name;

const RepClass: name;

const System.Reflection.MemberInfo: name;

const AssignToNonInvariantField: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Collections.IEnumerable: name;

const System.Reflection.IReflect: name;

const System.Boolean: name;

const System.IComparable: name;

const System.Exception: name;

const Microsoft.Contracts.GuardException: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

axiom !IsStaticField(AssignToNonInvariantField.y);

axiom IsDirectlyModifiableField(AssignToNonInvariantField.y);

axiom DeclType(AssignToNonInvariantField.y) == AssignToNonInvariantField;

axiom AsRangeField(AssignToNonInvariantField.y, System.Int32) == AssignToNonInvariantField.y;

axiom !IsStaticField(AssignToNonInvariantField.x);

axiom IsDirectlyModifiableField(AssignToNonInvariantField.x);

axiom DeclType(AssignToNonInvariantField.x) == AssignToNonInvariantField;

axiom AsRangeField(AssignToNonInvariantField.x, System.Int32) == AssignToNonInvariantField.x;

axiom !IsStaticField(InternalClass.X);

axiom IsDirectlyModifiableField(InternalClass.X);

axiom DeclType(InternalClass.X) == InternalClass;

axiom AsRangeField(InternalClass.X, System.Int32) == InternalClass.X;

axiom !IsStaticField(T.a);

axiom IsDirectlyModifiableField(T.a);

axiom DeclType(T.a) == T;

axiom AsRangeField(T.a, System.Int32) == T.a;

axiom !IsStaticField(T.b);

axiom IsDirectlyModifiableField(T.b);

axiom DeclType(T.b) == T;

axiom AsRangeField(T.b, System.Int32) == T.b;

axiom !IsStaticField(T.c0);

axiom IsDirectlyModifiableField(T.c0);

axiom DeclType(T.c0) == T;

axiom AsRangeField(T.c0, System.Int32) == T.c0;

axiom !IsStaticField(T.c1);

axiom IsDirectlyModifiableField(T.c1);

axiom DeclType(T.c1) == T;

axiom AsRangeField(T.c1, System.Int32) == T.c1;

axiom !IsStaticField(T.d);

axiom IsDirectlyModifiableField(T.d);

axiom DeclType(T.d) == T;

axiom AsRangeField(T.d, System.Int32) == T.d;

axiom !IsStaticField(T.e);

axiom IsDirectlyModifiableField(T.e);

axiom DeclType(T.e) == T;

axiom AsRangeField(T.e, System.Int32) == T.e;

axiom !IsStaticField(RepClass.Y);

axiom IsDirectlyModifiableField(RepClass.Y);

axiom DeclType(RepClass.Y) == RepClass;

axiom AsRangeField(RepClass.Y, System.Int32) == RepClass.Y;

axiom !IsStaticField(RepClass.X);

axiom IsDirectlyModifiableField(RepClass.X);

axiom DeclType(RepClass.X) == RepClass;

axiom AsRangeField(RepClass.X, System.Int32) == RepClass.X;

axiom !IsStaticField(RepClass.Z);

axiom IsDirectlyModifiableField(RepClass.Z);

axiom DeclType(RepClass.Z) == RepClass;

axiom AsRangeField(RepClass.Z, System.Int32) == RepClass.Z;

axiom !IsStaticField(ClientClass.r);

axiom IsDirectlyModifiableField(ClientClass.r);

axiom AsRepField(ClientClass.r, ClientClass) == ClientClass.r;

axiom DeclType(ClientClass.r) == ClientClass;

axiom AsNonNullRefField(ClientClass.r, RepClass) == ClientClass.r;

axiom !IsStaticField(AnotherClient.r);

axiom IsDirectlyModifiableField(AnotherClient.r);

axiom AsRepField(AnotherClient.r, AnotherClient) == AnotherClient.r;

axiom DeclType(AnotherClient.r) == AnotherClient;

axiom AsNonNullRefField(AnotherClient.r, RepClass) == AnotherClient.r;

axiom AssignToNonInvariantField <: AssignToNonInvariantField;

axiom $BaseClass(AssignToNonInvariantField) == System.Object;

axiom AssignToNonInvariantField <: $BaseClass(AssignToNonInvariantField) && AsDirectSubClass(AssignToNonInvariantField, $BaseClass(AssignToNonInvariantField)) == AssignToNonInvariantField;

axiom !$IsImmutable(AssignToNonInvariantField) && $AsMutable(AssignToNonInvariantField) == AssignToNonInvariantField;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: AssignToNonInvariantField } IsHeap($h) && $h[$oi, $inv] <: AssignToNonInvariantField && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, AssignToNonInvariantField.y]);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure AssignToNonInvariantField.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation AssignToNonInvariantField.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, SS$Display.Return.Local: bool where true, stack50000o: ref, stack0o: ref;

  entry:
    assume $IsNotNull(this, AssignToNonInvariantField);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block2006;

  block2006:
    goto block2023;

  block2023:
    // ----- load constant 0  ----- AssignToNonInvariantField.ssc(6,3)
    stack0i := 0;
    // ----- load field  ----- AssignToNonInvariantField.ssc(6,3)
    assert this != null;
    stack1i := $Heap[this, AssignToNonInvariantField.y];
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(6,3)
    // ----- branch  ----- AssignToNonInvariantField.ssc(6,3)
    goto true2023to2125, false2023to2040;

  true2023to2125:
    assume stack0i <= stack1i;
    goto block2125;

  false2023to2040:
    assume stack0i > stack1i;
    goto block2040;

  block2125:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block2142;

  block2040:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true2040to2091, false2040to2057;

  true2040to2091:
    assume !stack0b;
    goto block2091;

  false2040to2057:
    assume stack0b;
    goto block2057;

  block2091:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block2142;

  block2057:
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

  block2142:
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



procedure AssignToNonInvariantField.M(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AssignToNonInvariantField <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AssignToNonInvariantField.M(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, temp2: exposeVersionType, local4: int where InRange(local4, System.Int32), stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AssignToNonInvariantField);
    assume $Heap[this, $allocated] == true;
    goto block3162;

  block3162:
    goto block3315;

  block3315:
    // ----- nop
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(11,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(11,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AssignToNonInvariantField);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(11,13)
    stack1o := TypeObject(AssignToNonInvariantField);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(11,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AssignToNonInvariantField && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block3332;

  block3332:
    // ----- load field  ----- AssignToNonInvariantField.ssc(12,7)
    assert this != null;
    local3 := $Heap[this, AssignToNonInvariantField.x];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(12,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(12,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(12,7)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, AssignToNonInvariantField.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- load field  ----- AssignToNonInvariantField.ssc(13,7)
    assert this != null;
    local4 := $Heap[this, AssignToNonInvariantField.y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(13,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(13,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(13,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AssignToNonInvariantField) || $Heap[this, $localinv] == System.Object;
    $Heap[this, AssignToNonInvariantField.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- branch
    goto block3417;

  block3417:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true3417to3485, false3417to3434;

  true3417to3485:
    assume local2 == stack0o;
    goto block3485;

  false3417to3434:
    assume local2 != stack0o;
    goto block3434;

  block3485:
    // ----- load token  ----- AssignToNonInvariantField.ssc(14,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AssignToNonInvariantField);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(14,5)
    stack0o := TypeObject(AssignToNonInvariantField);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(14,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, AssignToNonInvariantField.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AssignToNonInvariantField ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block3468;

  block3434:
    // ----- is instance
    // ----- branch
    goto true3434to3485, false3434to3451;

  true3434to3485:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block3485;

  false3434to3451:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block3451;

  block3451:
    // ----- branch
    goto block3468;

  block3468:
    // ----- nop
    // ----- branch
    goto block3383;

  block3383:
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

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure AssignToNonInvariantField.N(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AssignToNonInvariantField <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AssignToNonInvariantField.N(this: ref)
{
  var local1: int where InRange(local1, System.Int32), stack0i: int, temp0: exposeVersionType, local2: int where InRange(local2, System.Int32);

  entry:
    assume $IsNotNull(this, AssignToNonInvariantField);
    assume $Heap[this, $allocated] == true;
    goto block4437;

  block4437:
    goto block4539;

  block4539:
    // ----- nop
    // ----- load field  ----- AssignToNonInvariantField.ssc(20,5)
    assert this != null;
    local1 := $Heap[this, AssignToNonInvariantField.x];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(20,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(20,5)
    stack0i := local1 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(20,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, AssignToNonInvariantField.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local1;
    // ----- load field  ----- AssignToNonInvariantField.ssc(21,5)
    assert this != null;
    local2 := $Heap[this, AssignToNonInvariantField.y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(21,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(21,5)
    stack0i := local2 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(21,5)
    assert this != null;
    assert !($Heap[this, $inv] <: AssignToNonInvariantField) || $Heap[this, $localinv] == System.Object;
    $Heap[this, AssignToNonInvariantField.y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- return
    return;

}



procedure AssignToNonInvariantField..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AssignToNonInvariantField && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AssignToNonInvariantField <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AssignToNonInvariantField..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, AssignToNonInvariantField);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, AssignToNonInvariantField.x] == 0;
    assume $Heap[this, AssignToNonInvariantField.y] == 0;
    goto block4981;

  block4981:
    goto block4998;

  block4998:
    // ----- call  ----- AssignToNonInvariantField.ssc(3,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block5066;

  block5066:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(3,38)
    temp0 := this;
    // ----- classic pack  ----- AssignToNonInvariantField.ssc(3,38)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, AssignToNonInvariantField.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AssignToNonInvariantField ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := AssignToNonInvariantField;
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



procedure AssignToNonInvariantField..cctor();
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



implementation AssignToNonInvariantField..cctor()
{

  entry:
    goto block5355;

  block5355:
    goto block5406;

  block5406:
    // ----- nop
    // ----- return
    return;

}



axiom InternalClass <: InternalClass;

axiom $BaseClass(InternalClass) == System.Object;

axiom InternalClass <: $BaseClass(InternalClass) && AsDirectSubClass(InternalClass, $BaseClass(InternalClass)) == InternalClass;

axiom !$IsImmutable(InternalClass) && $AsMutable(InternalClass) == InternalClass;

axiom (forall $U: name :: { $U <: InternalClass } $U <: InternalClass ==> $U == InternalClass);

procedure InternalClass.M(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != InternalClass.X) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation InternalClass.M(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, InternalClass);
    assume $Heap[this, $allocated] == true;
    goto block5610;

  block5610:
    goto block5627;

  block5627:
    // ----- load field  ----- AssignToNonInvariantField.ssc(31,5)
    assert this != null;
    local0 := $Heap[this, InternalClass.X];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(31,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(31,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(31,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, InternalClass.X] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(32,3)
    return;

}



procedure InternalClass..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == InternalClass && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(InternalClass <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation InternalClass..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, InternalClass);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, InternalClass.X] == 0;
    goto block5865;

  block5865:
    goto block5882;

  block5882:
    // ----- call  ----- AssignToNonInvariantField.ssc(25,7)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == InternalClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := InternalClass;
    assume IsHeap($Heap);
    return;

}



axiom T <: T;

axiom $BaseClass(T) == System.Object;

axiom T <: $BaseClass(T) && AsDirectSubClass(T, $BaseClass(T)) == T;

axiom !$IsImmutable(T) && $AsMutable(T) == T;

procedure T.Ma(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Ma(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block6052;

  block6052:
    goto block6069;

  block6069:
    // ----- load field  ----- AssignToNonInvariantField.ssc(46,5)
    assert this != null;
    local0 := $Heap[this, T.a];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(46,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(46,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(46,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, T.a] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(47,3)
    return;

}



procedure T.Mb(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Mb(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block6307;

  block6307:
    goto block6324;

  block6324:
    // ----- load field  ----- AssignToNonInvariantField.ssc(52,5)
    assert this != null;
    local0 := $Heap[this, T.b];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(52,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(52,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(52,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, T.b] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(53,3)
    return;

}



procedure T.Mc0(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Mc0(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block6562;

  block6562:
    goto block6579;

  block6579:
    // ----- load field  ----- AssignToNonInvariantField.ssc(58,5)
    assert this != null;
    local0 := $Heap[this, T.c0];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(58,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(58,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(58,5)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == System.Object;
    $Heap[this, T.c0] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(59,3)
    return;

}



procedure T.Mc1(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Mc1(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block6817;

  block6817:
    goto block6834;

  block6834:
    // ----- load field  ----- AssignToNonInvariantField.ssc(64,5)
    assert this != null;
    local0 := $Heap[this, T.c1];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(64,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(64,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(64,5)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == System.Object;
    $Heap[this, T.c1] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(65,3)
    return;

}



procedure T.Md(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Md(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block7072;

  block7072:
    goto block7089;

  block7089:
    // ----- load field  ----- AssignToNonInvariantField.ssc(70,5)
    assert this != null;
    local0 := $Heap[this, T.d];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(70,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(70,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(70,5)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == System.Object;
    $Heap[this, T.d] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(71,3)
    return;

}



procedure T.Me(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(T <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T.Me(this: ref)
{
  var local0: int where InRange(local0, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block7327;

  block7327:
    goto block7344;

  block7344:
    // ----- load field  ----- AssignToNonInvariantField.ssc(76,5)
    assert this != null;
    local0 := $Heap[this, T.e];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(76,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(76,5)
    stack0i := local0 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(76,5)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == System.Object;
    $Heap[this, T.e] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local0;
    // ----- return  ----- AssignToNonInvariantField.ssc(77,3)
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

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, T.a] == 0;
    assume $Heap[this, T.b] == 0;
    assume $Heap[this, T.c0] == 0;
    assume $Heap[this, T.c1] == 0;
    assume $Heap[this, T.d] == 0;
    assume $Heap[this, T.e] == 0;
    goto block7582;

  block7582:
    goto block7599;

  block7599:
    // ----- call  ----- AssignToNonInvariantField.ssc(35,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := T;
    assume IsHeap($Heap);
    return;

}



axiom RepClass <: RepClass;

axiom $BaseClass(RepClass) == System.Object;

axiom RepClass <: $BaseClass(RepClass) && AsDirectSubClass(RepClass, $BaseClass(RepClass)) == RepClass;

axiom !$IsImmutable(RepClass) && $AsMutable(RepClass) == RepClass;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: RepClass } IsHeap($h) && $h[$oi, $inv] <: RepClass && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, RepClass.Y]);

procedure RepClass.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation RepClass.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, RepClass);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block7888;

  block7888:
    goto block7905;

  block7905:
    // ----- load constant 0  ----- AssignToNonInvariantField.ssc(83,3)
    stack0i := 0;
    // ----- load field  ----- AssignToNonInvariantField.ssc(83,3)
    assert this != null;
    stack1i := $Heap[this, RepClass.Y];
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(83,3)
    // ----- branch  ----- AssignToNonInvariantField.ssc(83,3)
    goto true7905to8007, false7905to7922;

  true7905to8007:
    assume stack0i <= stack1i;
    goto block8007;

  false7905to7922:
    assume stack0i > stack1i;
    goto block7922;

  block8007:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block8024;

  block7922:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true7922to7973, false7922to7939;

  true7922to7973:
    assume !stack0b;
    goto block7973;

  false7922to7939:
    assume stack0b;
    goto block7939;

  block7973:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block8024;

  block7939:
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

  block8024:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

}



procedure RepClass.M(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(RepClass <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation RepClass.M(this: ref)
{
  var local1: int where InRange(local1, System.Int32), stack0i: int, temp0: exposeVersionType, local2: int where InRange(local2, System.Int32);

  entry:
    assume $IsNotNull(this, RepClass);
    assume $Heap[this, $allocated] == true;
    goto block8534;

  block8534:
    goto block8636;

  block8636:
    // ----- nop
    // ----- load field  ----- AssignToNonInvariantField.ssc(89,5)
    assert this != null;
    local1 := $Heap[this, RepClass.X];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(89,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(89,5)
    stack0i := local1 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(89,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    $Heap[this, RepClass.X] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local1;
    // ----- load field  ----- AssignToNonInvariantField.ssc(90,5)
    assert this != null;
    local2 := $Heap[this, RepClass.Z];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(90,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(90,5)
    stack0i := local2 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(90,5)
    assert this != null;
    assert !($Heap[this, $inv] <: RepClass) || $Heap[this, $localinv] == System.Object;
    $Heap[this, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- return
    return;

}



procedure RepClass.P(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(RepClass <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation RepClass.P(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), local3: int where InRange(local3, System.Int32), stack0i: int, temp2: exposeVersionType, local4: int where InRange(local4, System.Int32), local5: int where InRange(local5, System.Int32), stack0o: ref, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, RepClass);
    assume $Heap[this, $allocated] == true;
    goto block9333;

  block9333:
    goto block9486;

  block9486:
    // ----- nop
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(96,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(96,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(96,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(96,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block9503;

  block9503:
    // ----- load field  ----- AssignToNonInvariantField.ssc(97,7)
    assert this != null;
    local3 := $Heap[this, RepClass.X];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(97,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(97,7)
    stack0i := local3 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(97,7)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, RepClass.X] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- load field  ----- AssignToNonInvariantField.ssc(98,7)
    assert this != null;
    local4 := $Heap[this, RepClass.Y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(98,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(98,7)
    stack0i := local4 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(98,7)
    assert this != null;
    assert !($Heap[this, $inv] <: RepClass) || $Heap[this, $localinv] == System.Object;
    $Heap[this, RepClass.Y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local4;
    // ----- load field  ----- AssignToNonInvariantField.ssc(99,7)
    assert this != null;
    local5 := $Heap[this, RepClass.Z];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(99,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(99,7)
    stack0i := local5 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(99,7)
    assert this != null;
    assert !($Heap[this, $inv] <: RepClass) || $Heap[this, $localinv] == System.Object;
    $Heap[this, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block9588;

  block9588:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true9588to9656, false9588to9605;

  true9588to9656:
    assume local2 == stack0o;
    goto block9656;

  false9588to9605:
    assume local2 != stack0o;
    goto block9605;

  block9656:
    // ----- load token  ----- AssignToNonInvariantField.ssc(100,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(100,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(100,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block9639;

  block9605:
    // ----- is instance
    // ----- branch
    goto true9605to9656, false9605to9622;

  true9605to9656:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block9656;

  false9605to9622:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block9622;

  block9622:
    // ----- branch
    goto block9639;

  block9639:
    // ----- nop
    // ----- branch
    goto block9554;

  block9554:
    // ----- return
    return;

}



procedure RepClass..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == RepClass && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(RepClass <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation RepClass..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, RepClass);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, RepClass.X] == 0;
    assume $Heap[this, RepClass.Y] == 0;
    assume $Heap[this, RepClass.Z] == 0;
    goto block10676;

  block10676:
    goto block10693;

  block10693:
    // ----- call  ----- AssignToNonInvariantField.ssc(80,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block10761;

  block10761:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(80,21)
    temp0 := this;
    // ----- classic pack  ----- AssignToNonInvariantField.ssc(80,21)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := RepClass;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure RepClass..cctor();
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



implementation RepClass..cctor()
{

  entry:
    goto block11050;

  block11050:
    goto block11101;

  block11101:
    // ----- nop
    // ----- return
    return;

}



axiom ClientClass <: ClientClass;

axiom $BaseClass(ClientClass) == System.Object;

axiom ClientClass <: $BaseClass(ClientClass) && AsDirectSubClass(ClientClass, $BaseClass(ClientClass)) == ClientClass;

axiom !$IsImmutable(ClientClass) && $AsMutable(ClientClass) == ClientClass;

procedure ClientClass.M(this: ref);
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



implementation ClientClass.M(this: ref)
{
  var local0: ref where $Is(local0, RepClass), local1: int where InRange(local1, System.Int32), stack0i: int, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, ClientClass);
    assume $Heap[this, $allocated] == true;
    goto block11305;

  block11305:
    goto block11322;

  block11322:
    // ----- load field  ----- AssignToNonInvariantField.ssc(108,5)
    assert this != null;
    local0 := $Heap[this, ClientClass.r];
    // ----- load field  ----- AssignToNonInvariantField.ssc(108,5)
    assert local0 != null;
    local1 := $Heap[local0, RepClass.X];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(108,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(108,5)
    stack0i := local1 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(108,5)
    assert local0 != null;
    havoc temp0;
    $Heap[local0, $exposeVersion] := temp0;
    $Heap[local0, RepClass.X] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local1;
    // ----- return  ----- AssignToNonInvariantField.ssc(111,3)
    return;

}



procedure ClientClass.BadUpdateOfY(this: ref);
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



implementation ClientClass.BadUpdateOfY(this: ref)
{
  var local0: ref where $Is(local0, RepClass), local1: int where InRange(local1, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, ClientClass);
    assume $Heap[this, $allocated] == true;
    goto block11577;

  block11577:
    goto block11594;

  block11594:
    // ----- load field  ----- AssignToNonInvariantField.ssc(114,5)
    assert this != null;
    local0 := $Heap[this, ClientClass.r];
    // ----- load field  ----- AssignToNonInvariantField.ssc(114,5)
    assert local0 != null;
    local1 := $Heap[local0, RepClass.Y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(114,5)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(114,5)
    stack0i := local1 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(114,5)
    assert local0 != null;
    assert !($Heap[local0, $inv] <: RepClass) || $Heap[local0, $localinv] == System.Object;
    $Heap[local0, RepClass.Y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local1;
    // ----- return  ----- AssignToNonInvariantField.ssc(115,3)
    return;

}



procedure ClientClass.AnotherBadUpdateOfY(this: ref);
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



implementation ClientClass.AnotherBadUpdateOfY(this: ref)
{
  var local0: ref where $Is(local0, ClientClass), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, local1: ref where $Is(local1, RepClass), local2: int where InRange(local2, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, ClientClass);
    assume $Heap[this, $allocated] == true;
    goto block11917;

  block11917:
    goto block11985;

  block11985:
    // ----- copy  ----- AssignToNonInvariantField.ssc(118,13)
    local0 := this;
    // ----- copy  ----- AssignToNonInvariantField.ssc(118,13)
    stack0o := local0;
    // ----- load token  ----- AssignToNonInvariantField.ssc(118,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ClientClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(118,13)
    stack1o := TypeObject(ClientClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(118,13)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: ClientClass && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block12002;

  block12002:
    // ----- load field  ----- AssignToNonInvariantField.ssc(119,7)
    assert this != null;
    local1 := $Heap[this, ClientClass.r];
    // ----- load field  ----- AssignToNonInvariantField.ssc(119,7)
    assert local1 != null;
    local2 := $Heap[local1, RepClass.Y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(119,7)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(119,7)
    stack0i := local2 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(119,7)
    assert local1 != null;
    assert !($Heap[local1, $inv] <: RepClass) || $Heap[local1, $localinv] == System.Object;
    $Heap[local1, RepClass.Y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- branch
    goto block12053;

  block12053:
    // ----- copy  ----- AssignToNonInvariantField.ssc(120,5)
    stack0o := local0;
    // ----- load token  ----- AssignToNonInvariantField.ssc(120,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ClientClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(120,5)
    stack1o := TypeObject(ClientClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(120,5)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == ClientClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block12019;

  block12019:
    // ----- return  ----- AssignToNonInvariantField.ssc(121,3)
    return;

}



procedure ClientClass.GoodUpdateOfY(this: ref);
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



implementation ClientClass.GoodUpdateOfY(this: ref)
{
  var local0: ref where $Is(local0, ClientClass), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: ref, temp2: exposeVersionType, local3: ref where $Is(local3, System.Exception), local4: ref where $Is(local4, RepClass), local5: int where InRange(local5, System.Int32), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, ClientClass);
    assume $Heap[this, $allocated] == true;
    goto block12903;

  block12903:
    goto block12971;

  block12971:
    // ----- copy  ----- AssignToNonInvariantField.ssc(124,13)
    local0 := this;
    // ----- copy  ----- AssignToNonInvariantField.ssc(124,13)
    stack0o := local0;
    // ----- load token  ----- AssignToNonInvariantField.ssc(124,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ClientClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(124,13)
    stack1o := TypeObject(ClientClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(124,13)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: ClientClass && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block12988;

  block12988:
    // ----- serialized AssumeStatement  ----- AssignToNonInvariantField.ssc(125,7)
    assume TypeObject($typeof($Heap[this, ClientClass.r])) == TypeObject(RepClass);
    goto block13073;

  block13073:
    // ----- nop
    // ----- load field  ----- AssignToNonInvariantField.ssc(126,15)
    assert this != null;
    stack0o := $Heap[this, ClientClass.r];
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(126,15)
    temp1 := stack0o;
    // ----- load token  ----- AssignToNonInvariantField.ssc(126,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(126,15)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(126,15)
    assert temp1 != null;
    assert ($Heap[temp1, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp1, $ownerRef], $inv] <: $Heap[temp1, $ownerFrame]) || $Heap[$Heap[temp1, $ownerRef], $localinv] == $BaseClass($Heap[temp1, $ownerFrame])) && $Heap[temp1, $inv] <: RepClass && $Heap[temp1, $localinv] == $typeof(temp1);
    $Heap[temp1, $localinv] := System.Object;
    havoc temp2;
    $Heap[temp1, $exposeVersion] := temp2;
    assume IsHeap($Heap);
    local3 := null;
    goto block13090;

  block13090:
    // ----- load field  ----- AssignToNonInvariantField.ssc(127,9)
    assert this != null;
    local4 := $Heap[this, ClientClass.r];
    // ----- load field  ----- AssignToNonInvariantField.ssc(127,9)
    assert local4 != null;
    local5 := $Heap[local4, RepClass.Y];
    // ----- load constant 1  ----- AssignToNonInvariantField.ssc(127,9)
    stack0i := 1;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(127,9)
    stack0i := local5 + stack0i;
    // ----- store field  ----- AssignToNonInvariantField.ssc(127,9)
    assert local4 != null;
    assert !($Heap[local4, $inv] <: RepClass) || $Heap[local4, $localinv] == System.Object;
    $Heap[local4, RepClass.Y] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block13192;

  block13192:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true13192to13260, false13192to13209;

  true13192to13260:
    assume local3 == stack0o;
    goto block13260;

  false13192to13209:
    assume local3 != stack0o;
    goto block13209;

  block13260:
    // ----- load token  ----- AssignToNonInvariantField.ssc(130,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(130,7)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(130,7)
    assert temp1 != null;
    assert $Heap[temp1, $localinv] == System.Object;
    assert 0 <= $Heap[temp1, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp1 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp1, $localinv] := $typeof(temp1);
    assume IsHeap($Heap);
    goto block13243;

  block13209:
    // ----- is instance
    // ----- branch
    goto true13209to13260, false13209to13226;

  true13209to13260:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block13260;

  false13209to13226:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block13226;

  block13226:
    // ----- branch
    goto block13243;

  block13243:
    // ----- nop
    // ----- branch
    goto block13141;

  block13141:
    // ----- branch
    goto block13362;

  block13362:
    // ----- copy  ----- AssignToNonInvariantField.ssc(131,5)
    stack0o := local0;
    // ----- load token  ----- AssignToNonInvariantField.ssc(131,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ClientClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(131,5)
    stack1o := TypeObject(ClientClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(131,5)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == ClientClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block13158;

  block13158:
    // ----- return  ----- AssignToNonInvariantField.ssc(132,3)
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

procedure ClientClass..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == ClientClass && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(ClientClass <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ClientClass..ctor(this: ref)
{
  var stack50000o: ref, stack0o: ref;

  entry:
    assume $IsNotNull(this, ClientClass);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block14399;

  block14399:
    goto block14416;

  block14416:
    // ----- new object  ----- AssignToNonInvariantField.ssc(105,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(105,3)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(105,3)
    stack0o := stack50000o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(105,3)
    assert this != null;
    assert !($Heap[this, $inv] <: ClientClass) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == ClientClass);
    $Heap[this, ClientClass.r] := stack0o;
    call $UpdateOwnersForRep(this, ClientClass, stack0o);
    assume IsHeap($Heap);
    // ----- call  ----- AssignToNonInvariantField.ssc(104,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == ClientClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := ClientClass;
    assume IsHeap($Heap);
    return;

}



axiom AnotherClient <: AnotherClient;

axiom $BaseClass(AnotherClient) == System.Object;

axiom AnotherClient <: $BaseClass(AnotherClient) && AsDirectSubClass(AnotherClient, $BaseClass(AnotherClient)) == AnotherClient;

axiom !$IsImmutable(AnotherClient) && $AsMutable(AnotherClient) == AnotherClient;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: AnotherClient } IsHeap($h) && $h[$oi, $inv] <: AnotherClient && $h[$oi, $localinv] != System.Object ==> $h[$h[$oi, AnotherClient.r], RepClass.Z] == 12);

procedure AnotherClient.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation AnotherClient.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block14773;

  block14773:
    goto block14790;

  block14790:
    // ----- load field  ----- AssignToNonInvariantField.ssc(137,3)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- load field  ----- AssignToNonInvariantField.ssc(137,3)
    assert stack0o != null;
    stack0i := $Heap[stack0o, RepClass.Z];
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(137,3)
    stack1i := 12;
    // ----- binary operator  ----- AssignToNonInvariantField.ssc(137,3)
    // ----- branch  ----- AssignToNonInvariantField.ssc(137,3)
    goto true14790to14892, false14790to14807;

  true14790to14892:
    assume stack0i == stack1i;
    goto block14892;

  false14790to14807:
    assume stack0i != stack1i;
    goto block14807;

  block14892:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block14909;

  block14807:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true14807to14858, false14807to14824;

  true14807to14858:
    assume !stack0b;
    goto block14858;

  false14807to14824:
    assume stack0b;
    goto block14824;

  block14858:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block14909;

  block14824:
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

  block14909:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

}



procedure AnotherClient..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AnotherClient && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AnotherClient <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient..ctor(this: ref)
{
  var stack50000o: ref, stack0o: ref, stack1i: int, temp0: ref;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block15419;

  block15419:
    goto block15436;

  block15436:
    // ----- new object  ----- AssignToNonInvariantField.ssc(136,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(136,3)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(136,3)
    stack0o := stack50000o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(136,3)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- call  ----- AssignToNonInvariantField.ssc(139,39)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block15504;

  block15504:
    // ----- load field  ----- AssignToNonInvariantField.ssc(140,5)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(140,5)
    stack1i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(140,5)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: RepClass) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, RepClass.Z] := stack1i;
    assume IsHeap($Heap);
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(141,3)
    temp0 := this;
    // ----- classic pack  ----- AssignToNonInvariantField.ssc(141,3)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := AnotherClient;
    assume IsHeap($Heap);
    // ----- return  ----- AssignToNonInvariantField.ssc(141,3)
    return;

}



procedure AnotherClient..ctor$System.Int32(this: ref, q$in: int where InRange(q$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires 12 <= q$in && 2 * q$in <= 24;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == AnotherClient && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(AnotherClient <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient..ctor$System.Int32(this: ref, q$in: int)
{
  var q: int where InRange(q, System.Int32), stack50000o: ref, stack0o: ref, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0b: bool, stack0s: struct, temp2: ref;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    q := q$in;
    goto block16286;

  block16286:
    goto block16456;

  block16456:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(136,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(136,3)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(136,3)
    stack0o := stack50000o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(136,3)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- call  ----- AssignToNonInvariantField.ssc(144,5)
    assert this != null;
    call System.Object..ctor(this);
    $Heap[this, $NonNullFieldsAreInitialized] := true;
    assume IsHeap($Heap);
    goto block16524;

  block16524:
    // ----- load field  ----- AssignToNonInvariantField.ssc(146,13)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(146,13)
    temp0 := stack0o;
    // ----- load token  ----- AssignToNonInvariantField.ssc(146,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(146,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(146,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block16541;

  block16541:
    // ----- load field  ----- AssignToNonInvariantField.ssc(147,7)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- store field  ----- AssignToNonInvariantField.ssc(147,7)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: RepClass) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, RepClass.Z] := q;
    assume IsHeap($Heap);
    // ----- branch
    goto block16626;

  block16626:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true16626to16694, false16626to16643;

  true16626to16694:
    assume local3 == stack0o;
    goto block16694;

  false16626to16643:
    assume local3 != stack0o;
    goto block16643;

  block16694:
    // ----- load token  ----- AssignToNonInvariantField.ssc(148,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(148,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(148,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block16677;

  block16643:
    // ----- is instance
    // ----- branch
    goto true16643to16694, false16643to16660;

  true16643to16694:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block16694;

  false16643to16660:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block16660;

  block16660:
    // ----- branch
    goto block16677;

  block16677:
    // ----- nop
    // ----- branch
    goto block16592;

  block16592:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(149,3)
    temp2 := this;
    // ----- classic pack  ----- AssignToNonInvariantField.ssc(149,3)
    assert temp2 != null;
    assert $Heap[temp2, $inv] == System.Object && $Heap[temp2, $localinv] == $typeof(temp2);
    assert $Heap[$Heap[temp2, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $inv] := AnotherClient;
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure AnotherClient.M(this: ref);
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



implementation AnotherClient.M(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack0o: ref, stack1i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block17935;

  block17935:
    goto block18088;

  block18088:
    // ----- nop
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(152,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(152,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(152,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(152,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AnotherClient && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block18105;

  block18105:
    // ----- load field  ----- AssignToNonInvariantField.ssc(153,7)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(153,7)
    stack1i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(153,7)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: RepClass) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, RepClass.Z] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block18190;

  block18190:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true18190to18258, false18190to18207;

  true18190to18258:
    assume local2 == stack0o;
    goto block18258;

  false18190to18207:
    assume local2 != stack0o;
    goto block18207;

  block18258:
    // ----- load token  ----- AssignToNonInvariantField.ssc(154,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(154,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(154,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block18241;

  block18207:
    // ----- is instance
    // ----- branch
    goto true18207to18258, false18207to18224;

  true18207to18258:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block18258;

  false18207to18224:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block18224;

  block18224:
    // ----- branch
    goto block18241;

  block18241:
    // ----- nop
    // ----- branch
    goto block18156;

  block18156:
    // ----- return
    return;

}



procedure AnotherClient.P_Bad(this: ref);
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



implementation AnotherClient.P_Bad(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block19618;

  block19618:
    goto block19771;

  block19771:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(158,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(158,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(158,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(158,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(159,13)
    temp0 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(159,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(159,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(159,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block19788;

  block19788:
    // ----- load constant 20  ----- AssignToNonInvariantField.ssc(160,7)
    stack0i := 20;
    // ----- store field  ----- AssignToNonInvariantField.ssc(160,7)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block19873;

  block19873:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true19873to19941, false19873to19890;

  true19873to19941:
    assume local3 == stack0o;
    goto block19941;

  false19873to19890:
    assume local3 != stack0o;
    goto block19890;

  block19941:
    // ----- load token  ----- AssignToNonInvariantField.ssc(161,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(161,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(161,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block19924;

  block19890:
    // ----- is instance
    // ----- branch
    goto true19890to19941, false19890to19907;

  true19890to19941:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block19941;

  false19890to19907:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block19907;

  block19907:
    // ----- branch
    goto block19924;

  block19924:
    // ----- nop
    // ----- branch
    goto block19839;

  block19839:
    // ----- copy  ----- AssignToNonInvariantField.ssc(162,5)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(162,5)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure AnotherClient.P_AlsoBad(this: ref);
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



implementation AnotherClient.P_AlsoBad(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block21114;

  block21114:
    goto block21267;

  block21267:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(166,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(166,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(166,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(166,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(167,13)
    temp0 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(167,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(167,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(167,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block21284;

  block21284:
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(168,7)
    stack0i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(168,7)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block21369;

  block21369:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true21369to21437, false21369to21386;

  true21369to21437:
    assume local3 == stack0o;
    goto block21437;

  false21369to21386:
    assume local3 != stack0o;
    goto block21386;

  block21437:
    // ----- load token  ----- AssignToNonInvariantField.ssc(169,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(169,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(169,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block21420;

  block21386:
    // ----- is instance
    // ----- branch
    goto true21386to21437, false21386to21403;

  true21386to21437:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block21437;

  false21386to21403:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block21403;

  block21403:
    // ----- branch
    goto block21420;

  block21420:
    // ----- nop
    // ----- branch
    goto block21335;

  block21335:
    // ----- copy  ----- AssignToNonInvariantField.ssc(170,5)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(170,5)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- return
    return;

}



procedure AnotherClient.P_Good(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AnotherClient <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient.P_Good(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), stack0i: int, stack0b: bool, stack0s: struct, temp2: ref, temp3: exposeVersionType, local6: ref where $Is(local6, System.Exception);

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block22848;

  block22848:
    goto block23001;

  block23001:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(176,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(176,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(176,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(176,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(177,13)
    temp0 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(177,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(177,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(177,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block23018;

  block23018:
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(178,7)
    stack0i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(178,7)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block23171;

  block23171:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true23171to23239, false23171to23188;

  true23171to23239:
    assume local3 == stack0o;
    goto block23239;

  false23171to23188:
    assume local3 != stack0o;
    goto block23188;

  block23239:
    // ----- load token  ----- AssignToNonInvariantField.ssc(179,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(179,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(179,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block23222;

  block23188:
    // ----- is instance
    // ----- branch
    goto true23188to23239, false23188to23205;

  true23188to23239:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block23239;

  false23188to23205:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block23205;

  block23205:
    // ----- branch
    goto block23222;

  block23222:
    // ----- nop
    // ----- branch
    goto block23069;

  block23069:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(180,13)
    temp2 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(180,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(180,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(180,13)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: AnotherClient && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local6 := null;
    goto block23086;

  block23086:
    // ----- copy  ----- AssignToNonInvariantField.ssc(181,7)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(181,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block23341;

  block23341:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true23341to23409, false23341to23358;

  true23341to23409:
    assume local6 == stack0o;
    goto block23409;

  false23341to23358:
    assume local6 != stack0o;
    goto block23358;

  block23409:
    // ----- load token  ----- AssignToNonInvariantField.ssc(182,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(182,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(182,5)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert $Heap[$Heap[temp2, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block23392;

  block23358:
    // ----- is instance
    // ----- branch
    goto true23358to23409, false23358to23375;

  true23358to23409:
    assume $As(local6, Microsoft.Contracts.ICheckedException) != null;
    goto block23409;

  false23358to23375:
    assume $As(local6, Microsoft.Contracts.ICheckedException) == null;
    goto block23375;

  block23375:
    // ----- branch
    goto block23392;

  block23392:
    // ----- nop
    // ----- branch
    goto block23137;

  block23137:
    // ----- return
    return;

}



procedure AnotherClient.P_AlsoGood(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AnotherClient <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient.P_AlsoGood(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), temp2: ref, temp3: exposeVersionType, local5: ref where $Is(local5, System.Exception), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block25296;

  block25296:
    goto block25449;

  block25449:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(188,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(188,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(188,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(188,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(189,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(189,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(189,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(189,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AnotherClient && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block25466;

  block25466:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(190,15)
    temp2 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(190,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(190,15)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(190,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: RepClass && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local5 := null;
    goto block25483;

  block25483:
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(191,9)
    stack0i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(191,9)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block25619;

  block25619:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true25619to25687, false25619to25636;

  true25619to25687:
    assume local5 == stack0o;
    goto block25687;

  false25619to25636:
    assume local5 != stack0o;
    goto block25636;

  block25687:
    // ----- load token  ----- AssignToNonInvariantField.ssc(192,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(192,7)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(192,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert 0 <= $Heap[temp2, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block25670;

  block25636:
    // ----- is instance
    // ----- branch
    goto true25636to25687, false25636to25653;

  true25636to25687:
    assume $As(local5, Microsoft.Contracts.ICheckedException) != null;
    goto block25687;

  false25636to25653:
    assume $As(local5, Microsoft.Contracts.ICheckedException) == null;
    goto block25653;

  block25653:
    // ----- branch
    goto block25670;

  block25670:
    // ----- nop
    // ----- branch
    goto block25534;

  block25534:
    // ----- copy  ----- AssignToNonInvariantField.ssc(193,7)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(193,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block25789;

  block25789:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true25789to25857, false25789to25806;

  true25789to25857:
    assume local3 == stack0o;
    goto block25857;

  false25789to25806:
    assume local3 != stack0o;
    goto block25806;

  block25857:
    // ----- load token  ----- AssignToNonInvariantField.ssc(194,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(194,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(194,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block25840;

  block25806:
    // ----- is instance
    // ----- branch
    goto true25806to25857, false25806to25823;

  true25806to25857:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block25857;

  false25806to25823:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block25823;

  block25823:
    // ----- branch
    goto block25840;

  block25840:
    // ----- nop
    // ----- branch
    goto block25585;

  block25585:
    // ----- return
    return;

}



procedure AnotherClient.P_ViolatesInvariant(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AnotherClient <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient.P_ViolatesInvariant(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), temp2: ref, temp3: exposeVersionType, local5: ref where $Is(local5, System.Exception), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block27744;

  block27744:
    goto block27897;

  block27897:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(200,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(200,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(200,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(200,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(201,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(201,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(201,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(201,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AnotherClient && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block27914;

  block27914:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(202,15)
    temp2 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(202,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(202,15)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(202,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: RepClass && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local5 := null;
    goto block27931;

  block27931:
    // ----- load constant 20  ----- AssignToNonInvariantField.ssc(203,9)
    stack0i := 20;
    // ----- store field  ----- AssignToNonInvariantField.ssc(203,9)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block28067;

  block28067:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true28067to28135, false28067to28084;

  true28067to28135:
    assume local5 == stack0o;
    goto block28135;

  false28067to28084:
    assume local5 != stack0o;
    goto block28084;

  block28135:
    // ----- load token  ----- AssignToNonInvariantField.ssc(204,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(204,7)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(204,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert 0 <= $Heap[temp2, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block28118;

  block28084:
    // ----- is instance
    // ----- branch
    goto true28084to28135, false28084to28101;

  true28084to28135:
    assume $As(local5, Microsoft.Contracts.ICheckedException) != null;
    goto block28135;

  false28084to28101:
    assume $As(local5, Microsoft.Contracts.ICheckedException) == null;
    goto block28101;

  block28101:
    // ----- branch
    goto block28118;

  block28118:
    // ----- nop
    // ----- branch
    goto block27982;

  block27982:
    // ----- copy  ----- AssignToNonInvariantField.ssc(205,7)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(205,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block28237;

  block28237:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true28237to28305, false28237to28254;

  true28237to28305:
    assume local3 == stack0o;
    goto block28305;

  false28237to28254:
    assume local3 != stack0o;
    goto block28254;

  block28305:
    // ----- load token  ----- AssignToNonInvariantField.ssc(206,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(206,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(206,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block28288;

  block28254:
    // ----- is instance
    // ----- branch
    goto true28254to28305, false28254to28271;

  true28254to28305:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block28305;

  false28254to28271:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block28271;

  block28271:
    // ----- branch
    goto block28288;

  block28288:
    // ----- nop
    // ----- branch
    goto block28033;

  block28033:
    // ----- return
    return;

}



procedure AnotherClient.BadForAnotherReason(this: ref);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || !(AnotherClient <: DeclType($f))) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation AnotherClient.BadForAnotherReason(this: ref)
{
  var stack50000o: ref, stack0o: ref, newR: ref where $Is(newR, RepClass), temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local3: ref where $Is(local3, System.Exception), temp2: ref, temp3: exposeVersionType, local5: ref where $Is(local5, System.Exception), stack0i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block30192;

  block30192:
    goto block30345;

  block30345:
    // ----- nop
    // ----- new object  ----- AssignToNonInvariantField.ssc(212,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(212,5)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(212,5)
    stack0o := stack50000o;
    // ----- copy  ----- AssignToNonInvariantField.ssc(212,5)
    newR := stack0o;
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(213,13)
    temp0 := newR;
    // ----- load token  ----- AssignToNonInvariantField.ssc(213,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(213,13)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(213,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: RepClass && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local3 := null;
    goto block30362;

  block30362:
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(214,15)
    temp2 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(214,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(214,15)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(214,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: AnotherClient && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local5 := null;
    goto block30379;

  block30379:
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(215,9)
    stack0i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(215,9)
    assert newR != null;
    assert !($Heap[newR, $inv] <: RepClass) || $Heap[newR, $localinv] == System.Object;
    $Heap[newR, RepClass.Z] := stack0i;
    assume IsHeap($Heap);
    // ----- copy  ----- AssignToNonInvariantField.ssc(216,9)
    stack0o := newR;
    assert stack0o != null;
    stack0o := stack0o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(216,9)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block30515;

  block30515:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true30515to30583, false30515to30532;

  true30515to30583:
    assume local5 == stack0o;
    goto block30583;

  false30515to30532:
    assume local5 != stack0o;
    goto block30532;

  block30583:
    // ----- load token  ----- AssignToNonInvariantField.ssc(217,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(217,7)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(217,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert $Heap[$Heap[temp2, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block30566;

  block30532:
    // ----- is instance
    // ----- branch
    goto true30532to30583, false30532to30549;

  true30532to30583:
    assume $As(local5, Microsoft.Contracts.ICheckedException) != null;
    goto block30583;

  false30532to30549:
    assume $As(local5, Microsoft.Contracts.ICheckedException) == null;
    goto block30549;

  block30549:
    // ----- branch
    goto block30566;

  block30566:
    // ----- nop
    // ----- branch
    goto block30430;

  block30430:
    // ----- branch
    goto block30685;

  block30685:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true30685to30753, false30685to30702;

  true30685to30753:
    assume local3 == stack0o;
    goto block30753;

  false30685to30702:
    assume local3 != stack0o;
    goto block30702;

  block30753:
    // ----- load token  ----- AssignToNonInvariantField.ssc(218,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(218,5)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(218,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block30736;

  block30702:
    // ----- is instance
    // ----- branch
    goto true30702to30753, false30702to30719;

  true30702to30753:
    assume $As(local3, Microsoft.Contracts.ICheckedException) != null;
    goto block30753;

  false30702to30719:
    assume $As(local3, Microsoft.Contracts.ICheckedException) == null;
    goto block30719;

  block30719:
    // ----- branch
    goto block30736;

  block30736:
    // ----- nop
    // ----- branch
    goto block30481;

  block30481:
    // ----- return
    return;

}



procedure AnotherClient.UpdateTheRep_Bad(this: ref);
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



implementation AnotherClient.UpdateTheRep_Bad(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack50000o: ref, stack0o: ref, stack1i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block32402;

  block32402:
    goto block32555;

  block32555:
    // ----- nop
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(222,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(222,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(222,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(222,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AnotherClient && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block32572;

  block32572:
    // ----- new object  ----- AssignToNonInvariantField.ssc(223,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(223,7)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(223,7)
    stack0o := stack50000o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(223,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- load field  ----- AssignToNonInvariantField.ssc(224,7)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(224,7)
    stack1i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(224,7)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: RepClass) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, RepClass.Z] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block32657;

  block32657:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true32657to32725, false32657to32674;

  true32657to32725:
    assume local2 == stack0o;
    goto block32725;

  false32657to32674:
    assume local2 != stack0o;
    goto block32674;

  block32725:
    // ----- load token  ----- AssignToNonInvariantField.ssc(225,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(225,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(225,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block32708;

  block32674:
    // ----- is instance
    // ----- branch
    goto true32674to32725, false32674to32691;

  true32674to32725:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block32725;

  false32674to32691:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block32691;

  block32691:
    // ----- branch
    goto block32708;

  block32708:
    // ----- nop
    // ----- branch
    goto block32623;

  block32623:
    // ----- return
    return;

}



procedure AnotherClient.UpdateTheRep_Good(this: ref);
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



implementation AnotherClient.UpdateTheRep_Good(this: ref)
{
  var temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local2: ref where $Is(local2, System.Exception), stack50000o: ref, stack0o: ref, temp2: ref, temp3: exposeVersionType, local4: ref where $Is(local4, System.Exception), stack1i: int, stack0b: bool, stack0s: struct;

  entry:
    assume $IsNotNull(this, AnotherClient);
    assume $Heap[this, $allocated] == true;
    goto block34102;

  block34102:
    goto block34255;

  block34255:
    // ----- nop
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(229,13)
    temp0 := this;
    // ----- load token  ----- AssignToNonInvariantField.ssc(229,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(229,13)
    stack1o := TypeObject(AnotherClient);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(229,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: AnotherClient && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local2 := null;
    goto block34272;

  block34272:
    // ----- new object  ----- AssignToNonInvariantField.ssc(230,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == RepClass;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- AssignToNonInvariantField.ssc(230,7)
    assert stack50000o != null;
    call RepClass..ctor(stack50000o);
    // ----- copy  ----- AssignToNonInvariantField.ssc(230,7)
    stack0o := stack50000o;
    // ----- store field  ----- AssignToNonInvariantField.ssc(230,7)
    assert this != null;
    assert !($Heap[this, $inv] <: AnotherClient) || $Heap[this, $localinv] == System.Object;
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == AnotherClient);
    $Heap[this, AnotherClient.r] := stack0o;
    call $UpdateOwnersForRep(this, AnotherClient, stack0o);
    assume IsHeap($Heap);
    // ----- load field  ----- AssignToNonInvariantField.ssc(231,15)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- FrameGuard processing  ----- AssignToNonInvariantField.ssc(231,15)
    temp2 := stack0o;
    // ----- load token  ----- AssignToNonInvariantField.ssc(231,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(231,15)
    stack1o := TypeObject(RepClass);
    // ----- local unpack  ----- AssignToNonInvariantField.ssc(231,15)
    assert temp2 != null;
    assert ($Heap[temp2, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp2, $ownerRef], $inv] <: $Heap[temp2, $ownerFrame]) || $Heap[$Heap[temp2, $ownerRef], $localinv] == $BaseClass($Heap[temp2, $ownerFrame])) && $Heap[temp2, $inv] <: RepClass && $Heap[temp2, $localinv] == $typeof(temp2);
    $Heap[temp2, $localinv] := System.Object;
    havoc temp3;
    $Heap[temp2, $exposeVersion] := temp3;
    assume IsHeap($Heap);
    local4 := null;
    goto block34289;

  block34289:
    // ----- load field  ----- AssignToNonInvariantField.ssc(232,9)
    assert this != null;
    stack0o := $Heap[this, AnotherClient.r];
    // ----- load constant 12  ----- AssignToNonInvariantField.ssc(232,9)
    stack1i := 12;
    // ----- store field  ----- AssignToNonInvariantField.ssc(232,9)
    assert stack0o != null;
    assert !($Heap[stack0o, $inv] <: RepClass) || $Heap[stack0o, $localinv] == System.Object;
    $Heap[stack0o, RepClass.Z] := stack1i;
    assume IsHeap($Heap);
    // ----- branch
    goto block34425;

  block34425:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true34425to34493, false34425to34442;

  true34425to34493:
    assume local4 == stack0o;
    goto block34493;

  false34425to34442:
    assume local4 != stack0o;
    goto block34442;

  block34493:
    // ----- load token  ----- AssignToNonInvariantField.ssc(233,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, RepClass);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(233,7)
    stack0o := TypeObject(RepClass);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(233,7)
    assert temp2 != null;
    assert $Heap[temp2, $localinv] == System.Object;
    assert 0 <= $Heap[temp2, RepClass.Y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp2 && $Heap[$p, $ownerFrame] == RepClass ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp2, $localinv] := $typeof(temp2);
    assume IsHeap($Heap);
    goto block34476;

  block34442:
    // ----- is instance
    // ----- branch
    goto true34442to34493, false34442to34459;

  true34442to34493:
    assume $As(local4, Microsoft.Contracts.ICheckedException) != null;
    goto block34493;

  false34442to34459:
    assume $As(local4, Microsoft.Contracts.ICheckedException) == null;
    goto block34459;

  block34459:
    // ----- branch
    goto block34476;

  block34476:
    // ----- nop
    // ----- branch
    goto block34340;

  block34340:
    // ----- branch
    goto block34595;

  block34595:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true34595to34663, false34595to34612;

  true34595to34663:
    assume local2 == stack0o;
    goto block34663;

  false34595to34612:
    assume local2 != stack0o;
    goto block34612;

  block34663:
    // ----- load token  ----- AssignToNonInvariantField.ssc(234,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, AnotherClient);
    // ----- statically resolved GetTypeFromHandle call  ----- AssignToNonInvariantField.ssc(234,5)
    stack0o := TypeObject(AnotherClient);
    // ----- local pack  ----- AssignToNonInvariantField.ssc(234,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert $Heap[$Heap[temp0, AnotherClient.r], RepClass.Z] == 12;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == AnotherClient ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block34646;

  block34612:
    // ----- is instance
    // ----- branch
    goto true34612to34663, false34612to34629;

  true34612to34663:
    assume $As(local2, Microsoft.Contracts.ICheckedException) != null;
    goto block34663;

  false34612to34629:
    assume $As(local2, Microsoft.Contracts.ICheckedException) == null;
    goto block34629;

  block34629:
    // ----- branch
    goto block34646;

  block34646:
    // ----- nop
    // ----- branch
    goto block34391;

  block34391:
    // ----- return
    return;

}



procedure AnotherClient..cctor();
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



implementation AnotherClient..cctor()
{

  entry:
    goto block36006;

  block36006:
    goto block36057;

  block36057:
    // ----- nop
    // ----- return
    return;

}


