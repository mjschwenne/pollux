package main

import "unsafe"

type MyInt int

type Embedded struct {
	EmbeddedField int
}

type Named struct {
	NamedField uint
}

type AllKinds struct {
	Embedded
	BoolField        bool
	IntField         int
	MyIntField       MyInt
	Int8Field        int8
	Int16Field       int16
	Int32Field       int32
	Int64Field       int64
	UintField        uint
	Uint8Field       uint8
	Uint16Field      uint16
	Uint32Field      uint32
	Uint64Field      uint64
	UintptrField     uintptr
	Float32Field     float32
	Float64Field     float64
	Complex64Field   complex64
	Complex128Field  complex128
	ArrayField       [3]int // Array
	ChanField        chan int
	FuncField        func()
	InterfaceField   interface{}
	MapField         map[string]int
	PointerField     *int
	SliceField       []int
	StringField      string
	StructField      struct{ X int }
	NamedStructField Named
	UnsafePtrField   unsafe.Pointer
}
