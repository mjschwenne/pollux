package pollux

import (
	"context"
	"encoding/json"
	"fmt"
	"iter"
	"log"
	"strings"

	"github.com/bufbuild/protocompile"
	"github.com/bufbuild/protocompile/linker"
	"github.com/bufbuild/protocompile/walk"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protodesc"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/types/descriptorpb"
)

func MsgIter(file protoreflect.FileDescriptor) iter.Seq[protoreflect.MessageDescriptor] {
	return func(yield func(protoreflect.MessageDescriptor) bool) {
		for i := range file.Messages().Len() {
			if !yield(file.Messages().Get(i)) {
				return
			}
		}
	}
}

type Stats struct {
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

func stats_walker(s *Stats) func(n protoreflect.FullName, m proto.Message) error {
	return func(n protoreflect.FullName, m proto.Message) error {
		switch t := m.(type) {
		case *descriptorpb.DescriptorProto:
			s.MsgC += 1
			s.M_NestedEnumC += uint64(len(t.EnumType))
			s.M_NestedMsgC += uint64(len(t.NestedType))
			if len(t.GetReservedRange()) > 0 {
				s.M_ReservedRC += 1
			}
			if len(t.GetReservedName()) > 0 {
				s.M_ReservedNC += 1
			}
		case *descriptorpb.FieldDescriptorProto:
			s.FieldC += 1
			// All implicit fields show up with the OPTIONAL label, but have the
			// Proto3Optional field set to nil
			if t.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_OPTIONAL &&
				t.Proto3Optional == nil {
				s.F_ImpC += 1
			} else if t.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_REPEATED {
				s.F_RepC += 1
			} else {
				// Everything else should be explicitly marked as optional
				s.F_OptC += 1
			}
			switch t.GetType() {
			case descriptorpb.FieldDescriptorProto_TYPE_DOUBLE:
				s.F_DoubleC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_FLOAT:
				s.F_FloatC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_INT64:
				s.F_Int64C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_UINT64:
				s.F_Uint64C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_INT32:
				s.F_Int32C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_FIXED32:
				s.F_Fixed32C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_FIXED64:
				s.F_Fixed64C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_BOOL:
				s.F_BoolC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_STRING:
				s.F_StringC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_BYTES:
				s.F_BytesC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_MESSAGE:
				s.F_MessageC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_UINT32:
				s.F_Uint32C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_ENUM:
				s.F_EnumC += 1
			case descriptorpb.FieldDescriptorProto_TYPE_SFIXED64:
				s.F_Sfixed64C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_SFIXED32:
				s.F_Sfixed32C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_SINT64:
				s.F_Sint64C += 1
			case descriptorpb.FieldDescriptorProto_TYPE_SINT32:
				s.F_Sint32C += 1
			}
		case *descriptorpb.EnumDescriptorProto:
			s.EnumC += 1
			// Even if there are multiple reserved ranges,
			// just count this as "an enum which uses reserved fields"
			if len(t.GetReservedRange()) > 0 {
				s.E_ReservedRC += 1
			}
			if len(t.GetReservedName()) > 0 {
				s.E_ReservedNC += 1
			}
		case *descriptorpb.EnumValueDescriptorProto:
			s.E_EnumC += 1
		case *descriptorpb.OneofDescriptorProto:
			// Oneof fields with this prefix are *probably* implicit oneofs
			if !strings.HasPrefix(t.GetName(), "_optional_") {
				s.FieldC += 1
				s.F_OneofC += 1
			}
		case *descriptorpb.ServiceDescriptorProto:
			s.ServiceC += 1
		case *descriptorpb.MethodDescriptorProto:
			s.MethodC += 1
			if t.GetClientStreaming() {
				s.Me_CStreamC += 1
			}
			if t.GetServerStreaming() {
				s.Me_SStreamC += 1
			}
		default:
			fmt.Printf("Unknown Descriptor Type: %T -> %+v\n\n", m, m)
		}
		return nil
	}
}

func compile_protos(files []string) (linker.Files, error) {
	ctx := context.Background()
	compiler := protocompile.Compiler{
		Resolver: protocompile.WithStandardImports(&protocompile.SourceResolver{}),
	}
	return compiler.Compile(ctx, files...)
}

func ComputeStats(files []string) []byte {
	proto_descs, err := compile_protos(files)
	if err != nil {
		log.Fatalf("Error compiling protobuf files: %v\n", err)
	}

	stats := make(map[string]Stats)

	for _, fd := range proto_descs {
		s := Stats{}
		walk.DescriptorProtos(protodesc.ToFileDescriptorProto(fd), stats_walker(&s))
		stats[fd.Path()] = s
	}

	s_json, err := json.Marshal(stats)
	if err != nil {
		log.Fatalf("Cannot encode statistics into JSON: %v\n", err)
	}
	return s_json
}
