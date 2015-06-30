type real;

type elements;

type struct;

var $Heap: [ref,name]any;

function IsHeap(h: [ref,name]any) returns (bool);

const $allocated: name;

const $elements: name;

const $inv: name;

const $writable: name;

function ClassRepr(class: name) returns (ref);

axiom (forall c0: name, c1: name :: c0 != c1 ==> ClassRepr(c0) != ClassRepr(c1));

axiom (forall T: name :: !($typeof(ClassRepr(T)) <: System.Object));

axiom (forall T: name :: ClassRepr(T) != null);

axiom (forall T: name, h: [ref,name]any :: IsHeap(h) ==> cast(h[ClassRepr(T), $writable],bool));

function IsDirectlyModifiableField(f: name) returns (bool);

axiom !IsDirectlyModifiableField($allocated);

axiom IsDirectlyModifiableField($elements);

axiom !IsDirectlyModifiableField($inv);

axiom !IsDirectlyModifiableField($writable);

function IsStaticField(f: name) returns (bool);

axiom (forall T: name, h: [ref,name]any :: { h[ClassRepr(T), $writable] } IsHeap(h) ==> cast(h[ClassRepr(T), $writable],bool));

axiom !IsStaticField($allocated);

axiom !IsStaticField($elements);

axiom !IsStaticField($inv);

axiom !IsStaticField($writable);

function ValueArrayGet(elements, int) returns (any);

function ValueArraySet(elements, int, any) returns (elements);

function RefArrayGet(elements, int) returns (ref);

function RefArraySet(elements, int, ref) returns (elements);

axiom (forall A: elements, i: int, x: any :: ValueArrayGet(ValueArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: any :: i != j ==> ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j));

axiom (forall A: elements, i: int, x: ref :: RefArrayGet(RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j));

function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);

axiom (forall a: ref, d: int, x: int, y: int, x': int, y': int :: ArrayIndex(a, d, x, y) == ArrayIndex(a, d, x', y') ==> x == x' && y == y');

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,name]any :: $typeof(a) <: RefArray(T, r) ==> $Is(RefArrayGet(cast(heap[a, $elements],elements), i), T));

function $Rank(ref) returns (int);

axiom (forall a: ref :: 1 <= $Rank(a));

axiom (forall a: ref, T: name, r: int :: { $Is(a, ValueArray(T, r)) } $Is(a, ValueArray(T, r)) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $Is(a, RefArray(T, r)) } $Is(a, RefArray(T, r)) ==> $Rank(a) == r);

function $Length(ref) returns (int);

axiom (forall a: ref :: { $Length(a) } 0 <= $Length(a));

function $DimLength(ref, int) returns (int);

axiom (forall a: ref, i: int :: 0 <= $DimLength(a, i));

axiom (forall a: ref :: $Rank(a) == 1 ==> $DimLength(a, 0) == $Length(a));

function $LBound(ref, int) returns (int);

function $UBound(ref, int) returns (int);

axiom (forall a: ref, i: int :: { $LBound(a, i) } $LBound(a, i) == 0);

axiom (forall a: ref, i: int :: { $UBound(a, i) } $UBound(a, i) == $DimLength(a, i) - 1);

const System.Array: name;

axiom $IsClass(System.Array);

axiom System.Array <: System.Object;

axiom (forall T: name :: System.Array <: T ==> T == System.Array || System.Object <: T);

function $ElementType(name) returns (name);

function ValueArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { ValueArray(T, r) } ValueArray(T, r) <: System.Array);

function RefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { RefArray(T, r) } RefArray(T, r) <: System.Array);

axiom (forall T: name, U: name, r: int :: U <: T ==> RefArray(U, r) <: RefArray(T, r));

axiom (forall A: name, r: int :: $ElementType(ValueArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(RefArray(A, r)) == A);

axiom (forall A: name, r: int, T: name :: { T <: RefArray(A, r) } T <: RefArray(A, r) ==> T == RefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: ValueArray(A, r) } T <: ValueArray(A, r) ==> T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: RefArray(A, r) <: T ==> System.Array <: T || (T == RefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: ValueArray(A, r) <: T ==> System.Array <: T || T == ValueArray(A, r));

function $ArrayPtr(elementType: name) returns (name);

function $StructGet(struct, name) returns (any);

function $StructSet(struct, name, any) returns (struct);

axiom (forall s: struct, f: name, x: any :: $StructGet($StructSet(s, f, x), f) == x);

axiom (forall s: struct, f: name, f': name, x: any :: f != f' ==> $StructGet($StructSet(s, f, x), f') == $StructGet(s, f'));

function ZeroInit(s: struct, typ: name) returns (bool);

function $typeof(ref) returns (name);

function Implements(class: name, interface: name) returns (bool);

axiom (forall T: name, J: name :: { Implements(T, J) } Implements(T, J) ==> T <: J);

function InterfaceExtends(subIntf: name, superIntf: name) returns (bool);

axiom (forall J: name, K: name :: { InterfaceExtends(J, K) } InterfaceExtends(J, K) ==> J <: K);

function $IsClass(name) returns (bool);

function DirectBase(class: name) returns (directBaseClass: name);

axiom (forall C: name :: C <: DirectBase(C));

axiom (forall T: name, U: name :: $IsClass(T) && $IsClass(U) && T <: U ==> T == U || (T != System.Object && DirectBase(T) <: U));

function $IsInterface(name) returns (bool);

axiom (forall J: name :: { $IsInterface(J) } $IsInterface(J) ==> J <: System.Object);

function $IsValueType(name) returns (bool);

axiom (forall T: name :: $IsValueType(T) ==> (forall U: name :: T <: U ==> T == U) && (forall U: name :: U <: T ==> T == U));

axiom (forall T: name, U: name, o: ref :: o != null && $IsClass(T) && $IsClass(U) && !(T <: U) && !(U <: T) ==> !($Is(o, T) && $Is(o, U)));

const System.Object: name;

axiom $IsClass(System.Object);

function $IsTokenForType(struct, name) returns (bool);

function TypeObject(name) returns (ref);

const System.Type: name;

axiom System.Type <: System.Object;

axiom (forall T: name :: { TypeObject(T) } $IsNotNull(TypeObject(T), System.Type));

function $Is(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $Is(o, T) } $Is(o, T) <==> o == null || $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $IsNotNull(o, T) } $IsNotNull(o, T) <==> o != null && $Is(o, T));

function $As(ref, name) returns (ref);

axiom (forall o: ref, T: name :: $Is(o, T) ==> $As(o, T) == o);

axiom (forall o: ref, T: name :: !$Is(o, T) ==> $As(o, T) == null);

axiom (forall heap: [ref,name]any, o: ref, A: name, r: int :: $Is(o, RefArray(A, r)) ==> heap[o, $inv] == $typeof(o));

axiom (forall heap: [ref,name]any, o: ref, A: name, r: int :: IsHeap(heap) && o !=null && $Is(o, ValueArray(A, r)) ==> heap[o, $inv] == $typeof(o));

function IsAllocated(h: [ref,name]any, o: any) returns (bool);

axiom (forall h: [ref,name]any, o: ref, f: name :: { IsAllocated(h, h[o, f]) } IsHeap(h) ==> IsAllocated(h, h[o, f]));

axiom (forall h: [ref,name]any, s: struct, f: name :: { IsAllocated(h, $StructGet(s, f)) } IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f)));

axiom (forall h: [ref,name]any, e: elements, i: int :: { IsAllocated(h, RefArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i)));

axiom (forall h: [ref,name]any, o: ref :: { h[o, $allocated] } IsAllocated(h, o) ==> cast(h[o, $allocated],bool));

axiom (forall h: [ref,name]any, c: name :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> cast(h[ClassRepr(c), $allocated],bool));

function DeclType(field: name) returns (class: name);

function AsNonNullRefField(field: name, T: name) returns (f: name);

function AsRefField(field: name, T: name) returns (f: name);

function AsRangeField(field: name, T: name) returns (f: name);

axiom (forall f: name, T: name :: { AsNonNullRefField(f, T) } AsNonNullRefField(f, T) == f ==> AsRefField(f, T) == f);

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsRefField(f, T)] } IsHeap(h) ==> $Is(cast(h[o, AsRefField(f, T)],ref), T));

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsNonNullRefField(f, T)] } IsHeap(h) ==> cast(h[o, AsNonNullRefField(f, T)],ref) != null);

axiom (forall h: [ref,name]any, o: ref, f: name, T: name :: { h[o, AsRangeField(f, T)] } IsHeap(h) ==> InRange(cast(h[o, AsRangeField(f, T)],int), T));

function AsOwnedField(f: name) returns (name);

axiom (forall h: [ref,name]any, o: ref, f: name :: { h[o, AsOwnedField(f)] } IsHeap(h) && cast(h[o, $inv],name) <: DeclType(AsOwnedField(f)) ==> cast(h[o, AsOwnedField(f)],ref) == null || !cast(h[cast(h[o, AsOwnedField(f)],ref), $writable],bool));

axiom (forall h: [ref,name]any, o: ref :: { h[o, $writable] } IsHeap(h) && !cast(h[o, $writable],bool) ==> cast(h[o, $inv],name) == $typeof(o));

function Box(any, ref) returns (ref);

function Unbox(ref) returns (any);

axiom (forall x: any, p: ref :: { Unbox(Box(x, p)) } Unbox(Box(x, p)) == x);

axiom (forall heap: [ref,name]any, x: any, p: ref :: { heap[Box(x, p), $inv] } IsHeap(heap) ==> heap[Box(x, p), $inv] == $typeof(Box(x, p)));

function UnboxedType(ref) returns (name);

function BoxTester(p: ref, typ: name) returns (ref);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } UnboxedType(p) == typ <==> BoxTester(p, typ) != null);

const System.Int16: name;

axiom $IsValueType(System.Int16);

const System.Int32: name;

axiom $IsValueType(System.Int32);

const System.Int64: name;

axiom $IsValueType(System.Int64);

const System.Int16.MinValue: int;

const System.Int16.MaxValue: int;

const System.Int32.MinValue: int;

const System.Int32.MaxValue: int;

const System.Int64.MinValue: int;

const System.Int64.MaxValue: int;

axiom System.Int64.MinValue < System.Int32.MinValue;

axiom System.Int32.MinValue < System.Int16.MinValue;

axiom System.Int16.MinValue < System.Int16.MaxValue;

axiom System.Int16.MaxValue < System.Int32.MaxValue;

axiom System.Int32.MaxValue < System.Int64.MaxValue;

function InRange(i: int, T: name) returns (bool);

axiom (forall i: int :: InRange(i, System.Int16) <==> System.Int16.MinValue <= i && i <= System.Int16.MaxValue);

axiom (forall i: int :: InRange(i, System.Int32) <==> System.Int32.MinValue <= i && i <= System.Int32.MaxValue);

axiom (forall i: int :: InRange(i, System.Int64) <==> System.Int64.MinValue <= i && i <= System.Int64.MaxValue);

function $RealFromInt(real, int) returns (bool);

function $IntFromReal(int, real) returns (bool);

function $SizeIs(name, int) returns (bool);

function $IfThenElse(bool, any, any) returns (any);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } b ==> $IfThenElse(b, x, y) == x);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } !b ==> $IfThenElse(b, x, y) == y);

function #neg(int) returns (int);

function #rneg(real) returns (real);

function #rdiv(real, real) returns (real);

function #and(int, int) returns (int);

function #or(int, int) returns (int);

function #xor(int, int) returns (int);

function #shl(int, int) returns (int);

function #shr(int, int) returns (int);

axiom (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);

axiom (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);

axiom (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);

axiom (forall i: int :: { #shl(i, 0) } #shl(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shl(i, j + 1) == #shl(i, j) * 2);

axiom (forall i: int :: { #shr(i, 0) } #shr(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shr(i, j + 1) == #shr(i, j) / 2);

const $UnknownRef: ref;

const RTE.CallStack: name;

const RTE.Instructions: name;

const RTE.Data: name;

const RTE.MStackBase: name;

const RTE.CurrRTEMode: name;

const RTE.C: name;

const RTE.A: name;

const RTE.MSP: name;

const RTE.MStackMaxSize: name;

const RTE.CSP: name;

const RTE.Scratch: name;

const RTE.Program: name;

const RTE.Z: name;

const RTE.RtnCode: name;

const RTE.DPP: name;

const RTE.PC: name;

const Memory.contents: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const RTE: name;

const System.Boolean: name;

const System.Exception: name;

const Memory: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Byte: name;

const Microsoft.Contracts.GuardException: name;

const Microsoft.Contracts.ICheckedException: name;

const System.Runtime.InteropServices._Exception: name;

axiom !IsStaticField(Memory.contents);

axiom IsDirectlyModifiableField(Memory.contents);

axiom AsOwnedField(Memory.contents) == Memory.contents;

axiom DeclType(Memory.contents) == Memory;

axiom AsNonNullRefField(Memory.contents, ValueArray(System.Byte, 1)) == Memory.contents;

function #System.Array.get_Length(ref) returns (int);

function #Memory.get_cont$System.Int32([ref,name]any, ref, int) returns (int);

axiom !IsStaticField(RTE.CallStack);

axiom IsDirectlyModifiableField(RTE.CallStack);

axiom AsOwnedField(RTE.CallStack) == RTE.CallStack;

axiom DeclType(RTE.CallStack) == RTE;

axiom AsNonNullRefField(RTE.CallStack, ValueArray(System.Int32, 1)) == RTE.CallStack;

axiom !IsStaticField(RTE.CSP);

axiom IsDirectlyModifiableField(RTE.CSP);

axiom AsOwnedField(RTE.CSP) == RTE.CSP;

axiom DeclType(RTE.CSP) == RTE;

axiom AsRangeField(RTE.CSP, System.Int32) == RTE.CSP;

axiom !IsStaticField(RTE.MStackBase);

axiom IsDirectlyModifiableField(RTE.MStackBase);

axiom AsOwnedField(RTE.MStackBase) == RTE.MStackBase;

axiom DeclType(RTE.MStackBase) == RTE;

axiom AsRangeField(RTE.MStackBase, System.Int32) == RTE.MStackBase;

axiom !IsStaticField(RTE.MSP);

axiom IsDirectlyModifiableField(RTE.MSP);

axiom AsOwnedField(RTE.MSP) == RTE.MSP;

axiom DeclType(RTE.MSP) == RTE;

axiom AsRangeField(RTE.MSP, System.Int32) == RTE.MSP;

axiom !IsStaticField(RTE.MStackMaxSize);

axiom IsDirectlyModifiableField(RTE.MStackMaxSize);

axiom AsOwnedField(RTE.MStackMaxSize) == RTE.MStackMaxSize;

axiom DeclType(RTE.MStackMaxSize) == RTE;

axiom AsRangeField(RTE.MStackMaxSize, System.Int32) == RTE.MStackMaxSize;

axiom !IsStaticField(RTE.DPP);

axiom IsDirectlyModifiableField(RTE.DPP);

axiom AsOwnedField(RTE.DPP) == RTE.DPP;

axiom DeclType(RTE.DPP) == RTE;

axiom AsRangeField(RTE.DPP, System.Int32) == RTE.DPP;

axiom !IsStaticField(RTE.A);

axiom IsDirectlyModifiableField(RTE.A);

axiom AsOwnedField(RTE.A) == RTE.A;

axiom DeclType(RTE.A) == RTE;

axiom AsRangeField(RTE.A, System.Int32) == RTE.A;

axiom !IsStaticField(RTE.Z);

axiom IsDirectlyModifiableField(RTE.Z);

axiom AsOwnedField(RTE.Z) == RTE.Z;

axiom DeclType(RTE.Z) == RTE;

axiom !IsStaticField(RTE.C);

axiom IsDirectlyModifiableField(RTE.C);

axiom AsOwnedField(RTE.C) == RTE.C;

axiom DeclType(RTE.C) == RTE;

axiom !IsStaticField(RTE.PC);

axiom IsDirectlyModifiableField(RTE.PC);

axiom AsOwnedField(RTE.PC) == RTE.PC;

axiom DeclType(RTE.PC) == RTE;

axiom AsRangeField(RTE.PC, System.Int32) == RTE.PC;

axiom !IsStaticField(RTE.CurrRTEMode);

axiom IsDirectlyModifiableField(RTE.CurrRTEMode);

axiom AsOwnedField(RTE.CurrRTEMode) == RTE.CurrRTEMode;

axiom DeclType(RTE.CurrRTEMode) == RTE;

axiom AsRangeField(RTE.CurrRTEMode, System.Int32) == RTE.CurrRTEMode;

axiom !IsStaticField(RTE.RtnCode);

axiom IsDirectlyModifiableField(RTE.RtnCode);

axiom AsOwnedField(RTE.RtnCode) == RTE.RtnCode;

axiom DeclType(RTE.RtnCode) == RTE;

axiom AsRangeField(RTE.RtnCode, System.Int32) == RTE.RtnCode;

axiom !IsStaticField(RTE.Program);

axiom IsDirectlyModifiableField(RTE.Program);

axiom AsOwnedField(RTE.Program) == RTE.Program;

axiom DeclType(RTE.Program) == RTE;

axiom AsNonNullRefField(RTE.Program, Memory) == RTE.Program;

axiom !IsStaticField(RTE.Data);

axiom IsDirectlyModifiableField(RTE.Data);

axiom AsOwnedField(RTE.Data) == RTE.Data;

axiom DeclType(RTE.Data) == RTE;

axiom AsNonNullRefField(RTE.Data, Memory) == RTE.Data;

axiom !IsStaticField(RTE.Scratch);

axiom IsDirectlyModifiableField(RTE.Scratch);

axiom AsOwnedField(RTE.Scratch) == RTE.Scratch;

axiom DeclType(RTE.Scratch) == RTE;

axiom AsNonNullRefField(RTE.Scratch, Memory) == RTE.Scratch;

axiom !IsStaticField(RTE.Instructions);

axiom IsDirectlyModifiableField(RTE.Instructions);

axiom AsOwnedField(RTE.Instructions) == RTE.Instructions;

axiom DeclType(RTE.Instructions) == RTE;

axiom AsNonNullRefField(RTE.Instructions, ValueArray(System.Int32, 1)) == RTE.Instructions;

function #System.Array.get_Rank(ref) returns (int);

function #System.Array.GetLowerBound$System.Int32(ref, int) returns (int);

function #RTE.apply$System.Int32$System.Int32$System.Int32(int, int, int) returns (int);

function #RTE.carry$System.Int32$System.Int32$System.Int32(int, int, int) returns (bool);

function #RTE.DP([ref,name]any, ref) returns (int);

axiom $IsClass(Memory);

axiom DirectBase(Memory) == System.Object;

axiom (forall K: name :: { Memory <: K } Memory <: K <==> Memory == K || System.Object <: K);

axiom (forall U: name :: { U <: Memory } U <: Memory ==> U == Memory);

function Inv_Memory(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_Memory(this, heap) } Inv_Memory(this, heap) <==> true);

axiom (forall o: ref, heap: [ref,name]any :: { cast(heap[o, $inv],name) <: Memory } { Inv_Memory(o, heap) } IsHeap(heap) && cast(heap[o, $inv],name) <: Memory ==> Inv_Memory(o, heap));

procedure Memory..ctor$System.Int32(this: ref, n$in: int);
  requires 0 < n$in;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;



procedure System.Object..ctor(this: ref);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == System.Object;



procedure Memory.get_cont$System.Int32(this: ref, addr$in: int) returns ($result: int);
  requires 0 <= addr$in;
  requires addr$in < $Length(cast($Heap[this, Memory.contents],ref));
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures $Heap == old($Heap);
  free ensures $result == #Memory.get_cont$System.Int32($Heap, this, addr$in);
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;



procedure Memory.set_cont$System.Int32$System.Byte(this: ref, addr$in: int, value$in: int);
  requires 0 <= addr$in;
  requires addr$in < $Length(cast($Heap[this, Memory.contents],ref));
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;



procedure Memory.inSandbox$System.Int32(this: ref, addr$in: int) returns ($result: bool);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  ensures !$result || (0 <= addr$in && addr$in < $Length(cast($Heap[this, Memory.contents],ref)));
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Memory;



axiom $IsClass(RTE);

axiom DirectBase(RTE) == System.Object;

axiom (forall K: name :: { RTE <: K } RTE <: K <==> RTE == K || System.Object <: K);

function Inv_RTE(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_RTE(this, heap) } Inv_RTE(this, heap) <==> $Length(cast(heap[this, RTE.CallStack],ref)) == 10 && 0 <= cast(heap[this, RTE.CSP],int) && cast(heap[this, RTE.CSP],int) <= 10 && cast(heap[this, RTE.MStackBase],int) <= cast(heap[this, RTE.MSP],int) && cast(heap[this, RTE.MSP],int) <= cast(heap[this, RTE.MStackBase],int) + cast(heap[this, RTE.MStackMaxSize],int) && cast(heap[this, RTE.MSP],int) % 4 == 0 && cast(heap[this, RTE.MStackBase],int) % 4 == 0 && cast(heap[this, RTE.MStackMaxSize],int) % 4 == 0 && 0 <= cast(heap[this, RTE.MStackBase],int) && 0 <= cast(heap[this, RTE.MStackMaxSize],int) && 0 <= cast(heap[this, RTE.DPP],int));

axiom (forall o: ref, heap: [ref,name]any :: { cast(heap[o, $inv],name) <: RTE } { Inv_RTE(o, heap) } IsHeap(heap) && cast(heap[o, $inv],name) <: RTE ==> Inv_RTE(o, heap));

procedure RTE.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;



axiom $IsClass(Microsoft.Contracts.ObjectInvariantException);

axiom $IsClass(Microsoft.Contracts.GuardException);

axiom $IsClass(System.Exception);

axiom DirectBase(System.Exception) == System.Object;

axiom $IsInterface(System.Runtime.Serialization.ISerializable);

axiom (forall K: name :: { System.Runtime.Serialization.ISerializable <: K } System.Runtime.Serialization.ISerializable <: K <==> System.Runtime.Serialization.ISerializable == K || System.Object == K);

axiom Implements(System.Exception, System.Runtime.Serialization.ISerializable);

axiom $IsInterface(System.Runtime.InteropServices._Exception);

axiom (forall K: name :: { System.Runtime.InteropServices._Exception <: K } System.Runtime.InteropServices._Exception <: K <==> System.Runtime.InteropServices._Exception == K || System.Object == K);

axiom Implements(System.Exception, System.Runtime.InteropServices._Exception);

axiom (forall K: name :: { System.Exception <: K } System.Exception <: K <==> System.Exception == K || System.Object <: K || System.Runtime.Serialization.ISerializable <: K || System.Runtime.InteropServices._Exception <: K);

function Inv_System.Exception(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_System.Exception(this, heap) } Inv_System.Exception(this, heap) <==> true);

axiom (forall o: ref, heap: [ref,name]any :: { cast(heap[o, $inv],name) <: System.Exception } { Inv_System.Exception(o, heap) } IsHeap(heap) && cast(heap[o, $inv],name) <: System.Exception ==> Inv_System.Exception(o, heap));

axiom DirectBase(Microsoft.Contracts.GuardException) == System.Exception;

axiom (forall K: name :: { Microsoft.Contracts.GuardException <: K } Microsoft.Contracts.GuardException <: K <==> Microsoft.Contracts.GuardException == K || System.Exception <: K);

function Inv_Microsoft.Contracts.GuardException(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_Microsoft.Contracts.GuardException(this, heap) } Inv_Microsoft.Contracts.GuardException(this, heap) <==> true);

axiom (forall o: ref, heap: [ref,name]any :: { cast(heap[o, $inv],name) <: Microsoft.Contracts.GuardException } { Inv_Microsoft.Contracts.GuardException(o, heap) } IsHeap(heap) && cast(heap[o, $inv],name) <: Microsoft.Contracts.GuardException ==> Inv_Microsoft.Contracts.GuardException(o, heap));

axiom DirectBase(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.GuardException;

axiom (forall K: name :: { Microsoft.Contracts.ObjectInvariantException <: K } Microsoft.Contracts.ObjectInvariantException <: K <==> Microsoft.Contracts.ObjectInvariantException == K || Microsoft.Contracts.GuardException <: K);

function Inv_Microsoft.Contracts.ObjectInvariantException(object: ref, heap: [ref,name]any) returns (result: bool);

axiom (forall this: ref, heap: [ref,name]any :: { Inv_Microsoft.Contracts.ObjectInvariantException(this, heap) } Inv_Microsoft.Contracts.ObjectInvariantException(this, heap) <==> true);

axiom (forall o: ref, heap: [ref,name]any :: { cast(heap[o, $inv],name) <: Microsoft.Contracts.ObjectInvariantException } { Inv_Microsoft.Contracts.ObjectInvariantException(o, heap) } IsHeap(heap) && cast(heap[o, $inv],name) <: Microsoft.Contracts.ObjectInvariantException ==> Inv_Microsoft.Contracts.ObjectInvariantException(o, heap));

procedure Microsoft.Contracts.ObjectInvariantException..ctor(this: ref);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == Microsoft.Contracts.ObjectInvariantException;



procedure RTE..ctor$System.Int32.array$notnull$System.Int32$System.Int32(this: ref, input$in: ref, baseAddress$in: int, size$in: int);
  requires 0 <= baseAddress$in;
  requires baseAddress$in % 4 == 0;
  requires 0 <= size$in;
  requires size$in % 4 == 0;
  requires baseAddress$in + size$in <= 254;
  requires cast($Heap[input$in, $writable],bool) == true && cast($Heap[input$in, $inv],name) == $typeof(input$in);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;
  ensures cast($Heap[input$in, $writable],bool) == true && cast($Heap[input$in, $inv],name) == $typeof(input$in);



procedure System.Array.Copy$System.Array$notnull$System.Int32$System.Array$notnull$System.Int32$System.Int32(sourceArray$in: ref, sourceIndex$in: int, destinationArray$in: ref, destinationIndex$in: int, length$in: int);
  requires sourceArray$in != null;
  requires destinationArray$in != null;
  requires $Rank(sourceArray$in) == $Rank(destinationArray$in);
  requires sourceIndex$in >= $LBound(sourceArray$in, 0);
  requires destinationIndex$in >= $LBound(destinationArray$in, 0);
  requires length$in >= 0;
  requires sourceIndex$in + length$in <= $LBound(sourceArray$in, 0) + $Length(sourceArray$in);
  requires destinationIndex$in + length$in <= $LBound(destinationArray$in, 0) + $Length(destinationArray$in);
  requires cast($Heap[sourceArray$in, $writable],bool) == true && cast($Heap[sourceArray$in, $inv],name) == $typeof(sourceArray$in);
  requires cast($Heap[destinationArray$in, $writable],bool) == true && cast($Heap[destinationArray$in, $inv],name) == $typeof(destinationArray$in);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[sourceArray$in, $writable],bool) == true && cast($Heap[sourceArray$in, $inv],name) == $typeof(sourceArray$in);
  ensures cast($Heap[destinationArray$in, $writable],bool) == true && cast($Heap[destinationArray$in, $inv],name) == $typeof(destinationArray$in);



procedure RTE.apply$System.Int32$System.Int32$System.Int32(op$in: int, a$in: int, b$in: int) returns ($result: int);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures $Heap == old($Heap);
  free ensures $result == #RTE.apply$System.Int32$System.Int32$System.Int32(op$in, a$in, b$in);



procedure RTE.ApplyQuad$System.Int32$System.Int32$System.Int32(this: ref, op$in: int, a$in: int, b$in: int) returns ($result: int);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;



procedure RTE.carry$System.Int32$System.Int32$System.Int32(op$in: int, a$in: int, b$in: int) returns ($result: bool);
  requires op$in == 30 || op$in == 31;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures $Heap == old($Heap);
  free ensures $result == #RTE.carry$System.Int32$System.Int32$System.Int32(op$in, a$in, b$in);



procedure RTE.ReadQuad$Memory$notnull$System.Int32(m$in: ref, addr$in: int) returns ($result: int);
  requires 0 <= addr$in;
  requires addr$in <= $Length(cast($Heap[m$in, Memory.contents],ref)) - 4;
  requires cast($Heap[m$in, $writable],bool) == true && cast($Heap[m$in, $inv],name) == $typeof(m$in);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[m$in, $writable],bool) == true && cast($Heap[m$in, $inv],name) == $typeof(m$in);



procedure RTE.WriteQuad$Memory$notnull$System.Int32$System.Int32(m$in: ref, addr$in: int, value$in: int);
  requires 0 <= addr$in;
  requires addr$in <= $Length(cast($Heap[m$in, Memory.contents],ref)) - 4;
  requires cast($Heap[m$in, $writable],bool) == true && cast($Heap[m$in, $inv],name) == $typeof(m$in);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[m$in, $writable],bool) == true && cast($Heap[m$in, $inv],name) == $typeof(m$in);



procedure RTE.DP(this: ref) returns ($result: int);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == System.Object && cast($Heap[cast($Heap[this, RTE.Instructions],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.Instructions],ref), $inv],name) == $typeof(cast($Heap[this, RTE.Instructions],ref)) && cast($Heap[cast($Heap[this, RTE.Program],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.Program],ref), $inv],name) == $typeof(cast($Heap[this, RTE.Program],ref)) && cast($Heap[cast($Heap[this, RTE.Data],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.Data],ref), $inv],name) == $typeof(cast($Heap[this, RTE.Data],ref)) && cast($Heap[cast($Heap[this, RTE.Scratch],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.Scratch],ref), $inv],name) == $typeof(cast($Heap[this, RTE.Scratch],ref)) && cast($Heap[cast($Heap[this, RTE.CallStack],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.CallStack],ref), $inv],name) == $typeof(cast($Heap[this, RTE.CallStack],ref)) && Inv_RTE(this, $Heap) && cast($Heap[this, RTE.DPP],int) + 1 < $Length(cast($Heap[cast($Heap[this, RTE.Scratch],ref), Memory.contents],ref));
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures $Heap == old($Heap);
  free ensures $result == #RTE.DP($Heap, this);



procedure RTE.Terminate$System.Int32(this: ref, code$in: int);
  requires cast($Heap[this, $writable],bool) == true && System.Object <: cast($Heap[this, $inv],name);
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));



procedure RTE.Run(this: ref) returns ($result: int);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures IsAllocated($Heap, $result);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;



procedure RTE.ExecuteInstruction(this: ref);
  requires cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));
  ensures cast($Heap[this, $writable],bool) == true && cast($Heap[this, $inv],name) == RTE;



procedure RTE.ApplyALU$System.Int32$System.Int32$System.Int32(this: ref, opcd$in: int, valType$in: int, val$in: int);
  requires cast($Heap[this, $writable],bool) == true && System.Object <: cast($Heap[this, $inv],name) && cast($Heap[cast($Heap[this, RTE.Data],ref), $writable],bool) == true && cast($Heap[cast($Heap[this, RTE.Data],ref), $inv],name) == $typeof(cast($Heap[this, RTE.Data],ref));
  requires valType$in == 120 || valType$in == 121;
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));



implementation RTE.ExecuteInstruction(this: ref)
{
  var temp0: ref, local4: ref, stack0o: ref, stack1i: int, currInstr: int, opcd: int, oprnd: int, oprndType: int, local10: int, stack0i: int, stack0b: bool, stack2i: int, stack3o: ref, stack4i: int, stack5i: int, stack3i: int;

  entry:
    assume IsHeap($Heap);
    assume $IsNotNull(this, RTE);
    assume cast($Heap[this, $allocated],bool) == true;
    goto block48637;

  block48637:
    // ----- nop
    temp0 := this;
    // ----- unpack
    assert temp0 != null;
    assert cast($Heap[temp0, $writable],bool) == true && cast($Heap[temp0, $inv],name) == RTE;
    $Heap[temp0, $inv] := System.Object;
    $Heap[cast($Heap[temp0, RTE.Instructions],ref), $writable] := true;
    assume cast($Heap[cast($Heap[temp0, RTE.Instructions],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Instructions],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Instructions],ref));
    $Heap[cast($Heap[temp0, RTE.Program],ref), $writable] := true;
    assume cast($Heap[cast($Heap[temp0, RTE.Program],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Program],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Program],ref));
    $Heap[cast($Heap[temp0, RTE.Data],ref), $writable] := true;
    assume cast($Heap[cast($Heap[temp0, RTE.Data],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Data],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Data],ref));
    $Heap[cast($Heap[temp0, RTE.Scratch],ref), $writable] := true;
    assume cast($Heap[cast($Heap[temp0, RTE.Scratch],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Scratch],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Scratch],ref));
    $Heap[cast($Heap[temp0, RTE.CallStack],ref), $writable] := true;
    assume cast($Heap[cast($Heap[temp0, RTE.CallStack],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.CallStack],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.CallStack],ref));
    local4 := null;
    goto block48654;

  block48654:
    // ----- load field  ----- WindowsCard.ssc(362,9)
    assert this != null;
    stack0o := cast($Heap[this, RTE.Instructions],ref);
    assume $IsNotNull(stack0o, ValueArray(System.Int32, 1));
    // ----- load field  ----- WindowsCard.ssc(362,9)
    assert this != null;
    stack1i := cast($Heap[this, RTE.PC],int);
    assume InRange(stack1i, System.Int32);
    // ----- load element  ----- WindowsCard.ssc(362,9)
    assert stack0o != null;
    assert 0 <= stack1i;
    assert stack1i < $Length(stack0o);
    currInstr := cast(ValueArrayGet(cast($Heap[stack0o, $elements],elements), stack1i),int);
    // ----- copy  ----- WindowsCard.ssc(363,9)
    opcd := currInstr;
    // ----- load constant 0  ----- WindowsCard.ssc(364,9)
    oprnd := 0;
    // ----- load constant 0  ----- WindowsCard.ssc(365,9)
    oprndType := 0;
    // ----- serialized AssumeStatement  ----- WindowsCard.ssc(366,1)
    assume currInstr == 85;
    goto block48739;

  block48739:
    // ----- nop
    // ----- copy  ----- WindowsCard.ssc(367,18)
    local10 := currInstr;
    // ----- load constant 85
    stack0i := 85;
    // ----- binary operator
    stack0b := local10 == stack0i;
    // ----- branch
    goto true48739to48773, false48739to48756;

  true48739to48773:
    assume stack0b == true;
    goto block48773;

  false48739to48756:
    assume stack0b == false;
    goto block48756;

  block48773:
    // ----- load field  ----- WindowsCard.ssc(475,13)
    assert this != null;
    stack0i := cast($Heap[this, RTE.MSP],int);
    assume InRange(stack0i, System.Int32);
    // ----- load field  ----- WindowsCard.ssc(475,13)
    assert this != null;
    stack1i := cast($Heap[this, RTE.MStackBase],int);
    assume InRange(stack1i, System.Int32);
    // ----- binary operator  ----- WindowsCard.ssc(475,13)
    stack0b := stack0i == stack1i;
    // ----- branch  ----- WindowsCard.ssc(475,13)
    goto true48773to49113, false48773to48790;

  block48756:
    // ----- branch
    goto block49147;

  true48773to49113:
    assume stack0b == true;
    goto block49113;

  false48773to48790:
    assume stack0b == false;
    goto block48790;

  block49113:
    // ----- load constant 23  ----- WindowsCard.ssc(480,17)
    stack0i := 23;
    // ----- call  ----- WindowsCard.ssc(480,17)
    assert this != null;
    call RTE.Terminate$System.Int32(this, stack0i);
    // ----- nop  ----- WindowsCard.ssc(482,9)
    goto block49130;

  block48790:
    // ----- serialized AssumeStatement  ----- WindowsCard.ssc(476,17)
    assume cast($Heap[this, RTE.MStackBase],int) % 4 == 0 && cast($Heap[this, RTE.MSP],int) % 4 == 0 && cast($Heap[this, RTE.MStackBase],int) < cast($Heap[this, RTE.MSP],int) ==> cast($Heap[this, RTE.MStackBase],int) + 4 <= cast($Heap[this, RTE.MSP],int);
    goto block48807;

  block49147:
    // ----- branch
    goto block49232;

  block49232:
    stack0o := null;
    // ----- binary operator
    stack0b := local4 == stack0o;
    // ----- branch
    goto true49232to49300, false49232to49249;

  true49232to49300:
    assume stack0b == true;
    goto block49300;

  false49232to49249:
    assume stack0b == false;
    goto block49249;

  block49300:
    // ----- pack  ----- WindowsCard.ssc(630,5)
    assert temp0 != null;
    assert cast($Heap[temp0, $writable],bool) == true && System.Object <: cast($Heap[temp0, $inv],name);
    assert cast($Heap[temp0, $writable],bool) == true && cast($Heap[temp0, $inv],name) == System.Object;
    assert cast($Heap[cast($Heap[temp0, RTE.Instructions],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Instructions],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Instructions],ref));
    assert cast($Heap[cast($Heap[temp0, RTE.Program],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Program],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Program],ref));
    assert cast($Heap[cast($Heap[temp0, RTE.Data],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Data],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Data],ref));
    assert cast($Heap[cast($Heap[temp0, RTE.Scratch],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.Scratch],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.Scratch],ref));
    assert cast($Heap[cast($Heap[temp0, RTE.CallStack],ref), $writable],bool) == true && cast($Heap[cast($Heap[temp0, RTE.CallStack],ref), $inv],name) == $typeof(cast($Heap[temp0, RTE.CallStack],ref));
    assert Inv_RTE(temp0, $Heap);
    $Heap[cast($Heap[temp0, RTE.Instructions],ref), $writable] := false;
    $Heap[cast($Heap[temp0, RTE.Program],ref), $writable] := false;
    $Heap[cast($Heap[temp0, RTE.Data],ref), $writable] := false;
    $Heap[cast($Heap[temp0, RTE.Scratch],ref), $writable] := false;
    $Heap[cast($Heap[temp0, RTE.CallStack],ref), $writable] := false;
    $Heap[temp0, $inv] := RTE;
    goto block49283;

  block49249:
    // ----- is instance
    stack0o := $As(local4, Microsoft.Contracts.ICheckedException);
    // ----- branch
    goto true49249to49300, false49249to49266;

  block48807:
    goto block48824, block48926;

  block49130:
    // ----- branch  ----- WindowsCard.ssc(482,9)
    goto block49147;

  true49249to49300:
    assume stack0o != null;
    goto block49300;

  false49249to49266:
    assume stack0o == null;
    goto block49266;

  block49266:
    // ----- branch
    goto block49283;

  block48824:
    goto block48841, block48926;

  block48926:
    goto block48943;

  block49283:
    // ----- nop
    // ----- branch
    goto block49198;

  block48841:
    goto block48858, block48926;

  block48943:
    goto block48960, block48977;

  block49198:
    // ----- return
    return;

  block48858:
    goto block48875, block48892;

  block48960:
    goto block48977;

  block48977:
    goto block49011;

  block48875:
    goto block48909;

  block48892:
    goto block48909;

  block49011:
    // ----- nop
    // ----- serialized AssumeStatement  ----- WindowsCard.ssc(477,17)
    assume cast($Heap[this, RTE.MSP],int) <= $Length(cast($Heap[cast($Heap[this, RTE.Scratch],ref), Memory.contents],ref));
    goto block49028;

  block48909:
    goto block48943;

  block49028:
    goto block49045, block49062;

  block49045:
    goto block49062;

  block49062:
    goto block49096;

  block49096:
    // ----- nop
    // ----- load field  ----- WindowsCard.ssc(478,17)
    assert this != null;
    stack0o := cast($Heap[this, RTE.Scratch],ref);
    assume $IsNotNull(stack0o, Memory);
    // ----- load field  ----- WindowsCard.ssc(478,17)
    assert this != null;
    stack1i := cast($Heap[this, RTE.MSP],int);
    assume InRange(stack1i, System.Int32);
    // ----- load constant 4  ----- WindowsCard.ssc(478,17)
    stack2i := 4;
    // ----- binary operator  ----- WindowsCard.ssc(478,17)
    stack1i := stack1i - stack2i;
    // ----- load constant -1  ----- WindowsCard.ssc(478,17)
    stack2i := -1;
    // ----- load field  ----- WindowsCard.ssc(478,17)
    assert this != null;
    stack3o := cast($Heap[this, RTE.Scratch],ref);
    assume $IsNotNull(stack3o, Memory);
    // ----- load field  ----- WindowsCard.ssc(478,17)
    assert this != null;
    stack4i := cast($Heap[this, RTE.MSP],int);
    assume InRange(stack4i, System.Int32);
    // ----- load constant 4  ----- WindowsCard.ssc(478,17)
    stack5i := 4;
    // ----- binary operator  ----- WindowsCard.ssc(478,17)
    stack4i := stack4i - stack5i;
    // ----- call  ----- WindowsCard.ssc(478,17)
    call stack3i := RTE.ReadQuad$Memory$notnull$System.Int32(stack3o, stack4i);
    assume InRange(stack3i, System.Int32);
    // ----- binary operator  ----- WindowsCard.ssc(478,17)
    stack2i := stack2i * stack3i;
    // ----- call  ----- WindowsCard.ssc(478,17)
    call RTE.WriteQuad$Memory$notnull$System.Int32$System.Int32(stack0o, stack1i, stack2i);
    // ----- branch  ----- WindowsCard.ssc(479,15)
    goto block49130;

}



axiom $IsInterface(Microsoft.Contracts.ICheckedException);

axiom (forall K: name :: { Microsoft.Contracts.ICheckedException <: K } Microsoft.Contracts.ICheckedException <: K <==> Microsoft.Contracts.ICheckedException == K || System.Object == K);

procedure RTE..cctor();
  modifies $Heap;
  free ensures IsHeap($Heap);
  free ensures (forall $o: ref, $f: name :: $f != $inv && $o != null && cast(old($Heap)[$o, $allocated],bool) == true && cast(old($Heap)[$o, $writable],bool) == true && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) ==> old($Heap[$o, $f]) == $Heap[$o, $f]);
  free ensures (forall $o: ref :: old($Heap)[$o, $inv] == $Heap[$o, $inv] || cast(old($Heap)[$o, $allocated],bool) != true);
  free ensures (forall $o: ref :: cast(old($Heap)[$o, $allocated],bool) ==> cast($Heap[$o, $allocated],bool));


