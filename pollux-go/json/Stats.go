package pollux_json

import (
	"encoding/json"
	"go/types"
	"log"
	"reflect"
	"strings"

	"golang.org/x/tools/go/packages"
)

type JsonStats struct {
	StructC         uint64 `json:"struct_count_total"`
	S_Field         uint64 `json:"field_count_total"`
	S_Bool          uint64 `json:"field_count_bool"`
	S_Int           uint64 `json:"field_count_int"`
	S_Int8          uint64 `json:"field_count_int8"`
	S_Int16         uint64 `json:"field_count_int16"`
	S_Int32         uint64 `json:"field_count_int32"`
	S_Int64         uint64 `json:"field_count_int64"`
	S_Uint          uint64 `json:"field_count_uint"`
	S_Uint8         uint64 `json:"field_count_uint8"`
	S_Uint16        uint64 `json:"field_count_uint16"`
	S_Uint32        uint64 `json:"field_count_uint32"`
	S_Uint64        uint64 `json:"field_count_uint64"`
	S_Uintptr       uint64 `json:"field_count_uintptr"`
	S_Float32       uint64 `json:"field_count_float32"`
	S_Float64       uint64 `json:"field_count_float64"`
	S_Complex64     uint64 `json:"field_count_complex64"`
	S_Complex128    uint64 `json:"field_count_complex128"`
	S_UnsafePointer uint64 `json:"field_count_unsafe_pointer"`
	S_String        uint64 `json:"field_count_string"`
	S_Func          uint64 `json:"field_count_func"`
	S_Interface     uint64 `json:"field_count_interface"`
	S_Struct        uint64 `json:"field_count_struct"`
	S_ModifiedField uint64 `json:"field_count_modified_total"` // Modified fields count here and with the underlying type
	S_Array         uint64 `json:"field_count_modified_array"`
	S_Chan          uint64 `json:"field_count_modified_chan"`
	S_Map           uint64 `json:"field_count_modified_map"`
	S_Pointer       uint64 `json:"field_count_modified_pointer"`
	S_Slice         uint64 `json:"field_count_modified_slice"`
	TagC            uint64 `json:"tag_count_total"`
	T_OmitEmpty     uint64 `json:"tag_count_omitempty"`
	T_OmitZero      uint64 `json:"tag_count_omitzero"`
	T_Ingored       uint64 `json:"tag_count_ignored"`
	T_Named         uint64 `json:"tag_count_named"`
	T_String        uint64 `json:"tag_count_string"`
}

func mergeStats(dst, src *JsonStats) {
	dst.StructC += src.StructC
	dst.S_Field += src.S_Field
	dst.S_Bool += src.S_Bool
	dst.S_Int += src.S_Int
	dst.S_Int8 += src.S_Int8
	dst.S_Int16 += src.S_Int16
	dst.S_Int32 += src.S_Int32
	dst.S_Int64 += src.S_Int64
	dst.S_Uint += src.S_Uint
	dst.S_Uint8 += src.S_Uint8
	dst.S_Uint16 += src.S_Uint16
	dst.S_Uint32 += src.S_Uint32
	dst.S_Uint64 += src.S_Uint64
	dst.S_Uintptr += src.S_Uintptr
	dst.S_Float32 += src.S_Float32
	dst.S_Float64 += src.S_Float64
	dst.S_Complex64 += src.S_Complex64
	dst.S_Complex128 += src.S_Complex128
	dst.S_UnsafePointer += src.S_UnsafePointer
	dst.S_String += src.S_String
	dst.S_Func += src.S_Func
	dst.S_Interface += src.S_Interface
	dst.S_Struct += src.S_Struct
	dst.S_ModifiedField += src.S_ModifiedField
	dst.S_Array += src.S_Array
	dst.S_Chan += src.S_Chan
	dst.S_Map += src.S_Map
	dst.S_Pointer += src.S_Pointer
	dst.S_Slice += src.S_Slice
	dst.TagC += src.TagC
	dst.T_OmitEmpty += src.T_OmitEmpty
	dst.T_OmitZero += src.T_OmitZero
	dst.T_Ingored += src.T_Ingored
	dst.T_Named += src.T_Named
	dst.T_String += src.T_String
}

func ComputeStats(pkgPaths []string) []byte {
	cfg := &packages.Config{
		Mode: packages.NeedTypes | packages.NeedTypesInfo,
	}

	pkgs, err := packages.Load(cfg, pkgPaths...)
	if err != nil {
		log.Fatalf("Failed to load package: %v\n", err)
	}

	stats := make(map[string]JsonStats)
	for _, pkg := range pkgs {
		pkg_stats := &JsonStats{}
		scope := pkg.Types.Scope()
		for _, name := range scope.Names() {
			obj := scope.Lookup(name)
			tn, ok := obj.(*types.TypeName)
			if !ok {
				continue
			}

			st, ok := tn.Type().Underlying().(*types.Struct)
			if !ok {
				continue
			}

			struct_stats := &JsonStats{}
			count := structStats(struct_stats, st)

			if count {
				// fmt.Printf("Struct: %v\n", tn.Name())
				mergeStats(pkg_stats, struct_stats)
			}
		}
		stats[pkg.ID] = *pkg_stats
	}
	stats_as_json, err := json.Marshal(stats)
	if err != nil {
		log.Fatalf("Failed to encode stats as JSON: %v\n", err)
	}
	return stats_as_json
}

func addBasicType(stats *JsonStats, ty *types.Basic) {
	switch ty.Kind() {
	case types.Bool:
		stats.S_Bool += 1
	case types.Int:
		stats.S_Int += 1
	case types.Int8:
		stats.S_Int8 += 1
	case types.Int16:
		stats.S_Int16 += 1
	case types.Int32:
		stats.S_Int32 += 1
	case types.Int64:
		stats.S_Int64 += 1
	case types.Uint:
		stats.S_Uint += 1
	case types.Uint8:
		stats.S_Uint8 += 1
	case types.Uint16:
		stats.S_Uint16 += 1
	case types.Uint32:
		stats.S_Uint32 += 1
	case types.Uint64:
		stats.S_Uint64 += 1
	case types.Uintptr:
		stats.S_Uintptr += 1
	case types.Float32:
		stats.S_Float32 += 1
	case types.Float64:
		stats.S_Float64 += 1
	case types.Complex64:
		stats.S_Complex64 += 1
	case types.Complex128:
		stats.S_Complex128 += 1
	case types.String:
		stats.S_String += 1
	case types.UnsafePointer:
		stats.S_UnsafePointer += 1
	}
}

func fieldTypeStats(stats *JsonStats, ty types.Type) {
	// Since this is recursive, all the fields in the parent function
	switch t := ty.(type) {
	case *types.Basic:
		addBasicType(stats, t)
	case *types.Alias:
		// Hitting this case again should be impossible
		fieldTypeStats(stats, t.Underlying())
	case *types.Named:
		// Hitting this case again should be impossible
		fieldTypeStats(stats, t.Underlying())
	case *types.Array:
		stats.S_Array += 1
		stats.S_ModifiedField += 1
		fieldTypeStats(stats, t.Elem())
	case *types.Chan:
		stats.S_Chan += 1
		stats.S_ModifiedField += 1
		fieldTypeStats(stats, t.Elem())
	case *types.Signature:
		stats.S_Func += 1
	case *types.Interface:
		stats.S_Interface += 1
	case *types.Map:
		stats.S_Map += 1
		stats.S_ModifiedField += 1
		fieldTypeStats(stats, t.Key())
		fieldTypeStats(stats, t.Elem())
	case *types.Pointer:
		stats.S_Pointer += 1
		stats.S_ModifiedField += 1
		fieldTypeStats(stats, t.Elem())
	case *types.Struct:
		stats.S_Struct += 1
	case *types.Slice:
		stats.S_Slice += 1
		stats.S_ModifiedField += 1
		fieldTypeStats(stats, t.Elem())
	}
}

func jsonTagStats(stats *JsonStats, tag string) {
	// Simplest logic is to immediately check if the field is ignored...
	if tag == "-" {
		stats.T_Ingored += 1
		return
	}

	values := strings.Split(tag, ",")
	for i, t := range values {
		if i == 0 && t != "" {
			// First value is always the name
			stats.T_Named += 1
			continue
		}
		switch t {
		case "omitempty":
			stats.T_OmitEmpty += 1
		case "omitzero":
			stats.T_OmitZero += 1
		case "string":
			stats.T_String += 1
		}
	}
}

func structStats(stats *JsonStats, st *types.Struct) bool {
	uses_json := false
	stats.StructC += 1
	stats.S_Field += uint64(st.NumFields())
	for i := range st.NumFields() {
		f := st.Field(i)
		t := st.Tag(i)
		j, ok := reflect.StructTag(t).Lookup("json")
		if !uses_json && ok {
			uses_json = true
		}

		fieldTypeStats(stats, f.Type())
		if ok {
			stats.TagC += 1
			jsonTagStats(stats, j)
		}

	}

	return uses_json
}
