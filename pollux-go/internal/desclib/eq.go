package desclib

import (
	"iter"

	"google.golang.org/protobuf/reflect/protoreflect"
)

// Order insensitive equality over descriptors
func match_eq[TS any, T comparable](as TS, bs TS, mkIter func(TS) iter.Seq[T], eq func(a T, b T) bool) bool {
	b_matched := make(map[T]bool)

	for a := range mkIter(as) {
		a_matched := false
		for b := range mkIter(bs) {
			if b_matched[b] {
				continue
			}

			if eq(a, b) {
				b_matched[b] = true
				a_matched = true
			}
		}

		if !a_matched {
			return false
		}
	}

	// If we get here, every element of as has been matched.
	// Now check that every element of bs has been matched.
	for b := range mkIter(bs) {
		if _, ok := b_matched[b]; !ok {
			return false
		}
	}

	return true
}

func FieldDescEq(a protoreflect.FieldDescriptor, b protoreflect.FieldDescriptor) (result bool) {
	result = true
	result = result && (a.Number() == b.Number())
	result = result && (a.Cardinality() == b.Cardinality())
	result = result && (a.HasOptionalKeyword() == b.HasOptionalKeyword())
	result = result && (a.Kind() == b.Kind())
	if a.Kind() == protoreflect.MessageKind && b.Kind() == protoreflect.MessageKind {
		result = result && (a.Message().Name() == b.Message().Name())
	}
	result = result && (a.Name() == b.Name())
	return
}

// Primitive equality functions
// At the moment, only looks at field definitions
func MessageDescEq(a protoreflect.MessageDescriptor, b protoreflect.MessageDescriptor) (result bool) {
	result = a.Name() == b.Name()
	a_fields := a.Fields()
	b_fields := b.Fields()
	result = result && a_fields.Len() == b_fields.Len()
	// Only need to compare fields if they could still be equal
	if !result {
		return false
	}

	return match_eq(a, b, FieldIter, FieldDescEq)
}

func EnumValueDescEq(a protoreflect.EnumValueDescriptor, b protoreflect.EnumValueDescriptor) (result bool) {
	result = a.Number() == b.Number()
	result = result && a.Name() == b.Name()
	return
}

func EnumDescEq(a protoreflect.EnumDescriptor, b protoreflect.EnumDescriptor) bool {
	return match_eq(a, b, ValueIter, EnumValueDescEq)
}

// Only looks at messages right now, but is insensitive to ordering (I hope)
func FileDescEq(a protoreflect.FileDescriptor, b protoreflect.FileDescriptor) bool {
	return match_eq(a, b, MsgIter, MessageDescEq) && match_eq(a, b, EnumIter, EnumDescEq)
}
