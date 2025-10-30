package pollux_proto

import (
	"encoding/json"
	"fmt"
	"log"
	"strings"

	"github.com/bufbuild/protocompile/walk"
	"google.golang.org/protobuf/reflect/protoreflect"

	"github.com/mjschwenne/pollux/internal/desclib"
)

type ProtoStats struct {
	MsgC          uint64 `json:"message_count_total"`
	M_NestedEnumC uint64 `json:"message_count_nested_enum"`
	// Includes the count of maps
	// which are apparently internally represented as a nested message
	M_NestedMsgC uint64 `json:"message_count_nested_msg"`
	M_ReservedRC uint64 `json:"message_count_reserved_range"`
	M_ReservedNC uint64 `json:"message_count_reserved_name"`
	FieldC       uint64 `json:"field_count_total"`
	F_DoubleC    uint64 `json:"field_count_double"`
	F_FloatC     uint64 `json:"field_count_float"`
	F_Int64C     uint64 `json:"field_count_int64"`
	F_Uint64C    uint64 `json:"field_count_uint64"`
	F_Int32C     uint64 `json:"field_count_int32"`
	F_Fixed64C   uint64 `json:"field_count_fixed64"`
	F_Fixed32C   uint64 `json:"field_count_fixed32"`
	F_BoolC      uint64 `json:"field_count_bool"`
	F_StringC    uint64 `json:"field_count_string"`
	F_MessageC   uint64 `json:"field_count_message"`
	F_BytesC     uint64 `json:"field_count_bytes"`
	F_Uint32C    uint64 `json:"field_count_uint32"`
	F_EnumC      uint64 `json:"field_count_enum"`
	F_Sfixed64C  uint64 `json:"field_count_sfixed64"`
	F_Sfixed32C  uint64 `json:"field_count_sfixed32"`
	F_Sint64C    uint64 `json:"field_count_sint64"`
	F_Sint32C    uint64 `json:"field_count_sint32"`
	F_OneofC     uint64 `json:"field_count_oneof"`
	F_ImpC       uint64 `json:"field_count_implicit"`
	F_OptC       uint64 `json:"field_count_optional"`
	// All map fields will be counted here
	F_RepC       uint64 `json:"field_count_repeated"`
	EnumC        uint64 `json:"enum_count_total"`
	E_EnumC      uint64 `json:"enum_count_value"`
	E_ReservedRC uint64 `json:"enum_count_reserved_range"`
	E_ReservedNC uint64 `json:"enum_count_reserved_name"`
	ServiceC     uint64 `json:"service_count_total"`
	MethodC      uint64 `json:"method_count_total"`
	Me_CStreamC  uint64 `json:"method_count_client_streaming"`
	Me_SStreamC  uint64 `json:"method_count_server_streaming"`
}

func stats_walker(s *ProtoStats) func(d protoreflect.Descriptor) error {
	return func(d protoreflect.Descriptor) error {
		switch t := d.(type) {
		case protoreflect.MessageDescriptor:
			s.MsgC += 1
			s.M_NestedEnumC += uint64(t.Enums().Len())
			s.M_NestedMsgC += uint64(t.Messages().Len())
			if t.ReservedNames().Len() > 0 {
				s.M_ReservedNC += 1
			}
			if t.ReservedRanges().Len() > 0 {
				s.M_ReservedRC += 1
			}
		case protoreflect.FieldDescriptor:
			s.FieldC += 1
			if t.HasOptionalKeyword() {
				s.F_OptC += 1
			} else if t.Cardinality() == protoreflect.Repeated {
				s.F_RepC += 1
			} else {
				s.F_ImpC += 1
			}
			switch t.Kind() {
			case protoreflect.DoubleKind:
				s.F_DoubleC += 1
			case protoreflect.FloatKind:
				s.F_FloatC += 1
			case protoreflect.Int64Kind:
				s.F_Int64C += 1
			case protoreflect.Uint64Kind:
				s.F_Uint64C += 1
			case protoreflect.Int32Kind:
				s.F_Int32C += 1
			case protoreflect.Fixed32Kind:
				s.F_Fixed32C += 1
			case protoreflect.Fixed64Kind:
				s.F_Fixed64C += 1
			case protoreflect.BoolKind:
				s.F_BoolC += 1
			case protoreflect.StringKind:
				s.F_StringC += 1
			case protoreflect.BytesKind:
				s.F_BytesC += 1
			case protoreflect.MessageKind:
				s.F_MessageC += 1
			case protoreflect.Uint32Kind:
				s.F_Uint32C += 1
			case protoreflect.EnumKind:
				s.F_EnumC += 1
			case protoreflect.Sfixed64Kind:
				s.F_Sfixed64C += 1
			case protoreflect.Sfixed32Kind:
				s.F_Sfixed32C += 1
			case protoreflect.Sint64Kind:
				s.F_Sint64C += 1
			case protoreflect.Sint32Kind:
				s.F_Sint32C += 1
			}
		case protoreflect.EnumDescriptor:
			s.EnumC += 1
			// Even if there are multiple reserved ranges,
			// just count this as "an enum which uses reserved fields"
			if t.ReservedRanges().Len() > 0 {
				s.E_ReservedRC += 1
			}
			if t.ReservedNames().Len() > 0 {
				s.E_ReservedNC += 1
			}
		case protoreflect.EnumValueDescriptor:
			s.E_EnumC += 1
		case protoreflect.OneofDescriptor:
			// Oneof fields with this prefix are *probably* implicit onesof..
			if !strings.HasPrefix(string(t.Name()), "_optional_") {
				s.FieldC += 1
				s.F_OneofC += 1
			}
		case protoreflect.ServiceDescriptor:
			s.ServiceC += 1
		case protoreflect.MethodDescriptor:
			s.MethodC += 1
			if t.IsStreamingClient() {
				s.Me_CStreamC += 1
			}
			if t.IsStreamingServer() {
				s.Me_SStreamC += 1
			}
		default:
			fmt.Printf("Unknown Descriptor Type: %T -> %+v\n\n", t, t)
		}
		return nil
	}
}

func ComputeStats(files []string) []byte {
	proto_descs, err := desclib.CompileProtos(files)
	if err != nil {
		log.Fatalf("Error compiling protobuf files: %v\n", err)
	}

	stats := make(map[string]ProtoStats)

	for _, fd := range proto_descs {
		s := ProtoStats{}
		walk.Descriptors(fd, stats_walker(&s))
		stats[fd.Path()] = s
	}

	s_json, err := json.Marshal(stats)
	if err != nil {
		log.Fatalf("Cannot encode statistics into JSON: %v\n", err)
	}
	return s_json
}
