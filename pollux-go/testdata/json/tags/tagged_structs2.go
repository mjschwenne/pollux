package main

import "time"

// NoTags struct without any tags
type NoTags struct {
	Field1 string
	Field2 int
	Field3 bool
}

// MixedTags with some tagged and some untagged fields
type MixedTags struct {
	Tagged     string `json:"tagged"`
	Untagged   string
	AlsoTagged int `json:"also_tagged" validate:"required"`
}

// ProtobufExample with protobuf tags
type ProtobufExample struct {
	ID    uint32 `protobuf:"varint,1,opt,name=id,proto3" json:"id,omitempty"`
	Name  string `protobuf:"bytes,2,opt,name=name,proto3" json:"name,omitempty"`
	Count int64  `protobuf:"varint,3,opt,name=count,proto3" json:"count,omitempty"`
}
