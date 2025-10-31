package main

import "unsafe"

type MyInt int

type AliasedInt = int

type Embedded struct {
	EmbeddedField int
}

type Named struct {
	NamedField uint
}

type AllKinds struct {
	Embedded         `json:"-"`
	BoolField        bool            `json:"bool,omitzero"`
	IntField         int             `json:"-"`
	MyIntField       MyInt           `json:"-"`
	AliasedField     AliasedInt      `json:"-"`
	Int8Field        int8            `json:"-"`
	Int16Field       int16           `json:"-"`
	Int32Field       int32           `json:"-"`
	Int64Field       int64           `json:"int64,string"`
	UintField        uint            `json:"-"`
	Uint8Field       uint8           `json:"-"`
	Uint16Field      uint16          `json:"-"`
	Uint32Field      uint32          `json:"-"`
	Uint64Field      uint64          `json:"-"`
	UintptrField     uintptr         `json:"-"`
	Float32Field     float32         `json:"-"`
	Float64Field     float64         `json:"-"`
	Complex64Field   complex64       `json:"-"`
	Complex128Field  complex128      `json:"-"`
	ArrayField       [3]int          `json:"-"` // Array
	ChanField        chan int        `json:"-"`
	FuncField        func()          `json:"-"`
	InterfaceField   interface{}     `json:"-"`
	MapField         map[string]int  `json:"-"`
	PointerField     *int            `json:"-"`
	SliceField       []int           `json:"slice,omitempty"`
	StringField      string          `json:"-"`
	StructField      struct{ X int } `json:"-"`
	NamedStructField Named
	UnsafePtrField   unsafe.Pointer `json:"-,"`
}
