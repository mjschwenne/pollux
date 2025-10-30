package pollux_json

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"log"
)

type JsonStats struct {
	StructC         uint64
	S_Field         uint64
	S_Bool          uint64
	S_Int           uint64
	S_Int8          uint64
	S_Int16         uint64
	S_Int32         uint64
	S_Int64         uint64
	S_Uint          uint64
	S_Uint8         uint64
	S_Uint16        uint64
	S_Uint32        uint64
	S_Uint64        uint64
	S_Uintptr       uint64
	S_Float32       uint64
	S_Float64       uint64
	S_Complex64     uint64
	S_Complex128    uint64
	S_Array         uint64
	S_Chan          uint64
	S_Func          uint64
	S_Interface     uint64
	S_Map           uint64
	S_Pointer       uint64 // Pointer fields add here and two the underlying type
	S_Slice         uint64
	S_Struct        uint64
	S_AnonStruct    uint64
	S_UnsafePointer uint64
	TagC            uint64
	T_OmitEmpty     uint64
	T_OmitZero      uint64
	T_Ingored       uint64
	T_Named         uint64
	T_String        uint64
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
	dst.S_Array += src.S_Array
	dst.S_Chan += src.S_Chan
	dst.S_Func += src.S_Func
	dst.S_Interface += src.S_Interface
	dst.S_Map += src.S_Map
	dst.S_Pointer += src.S_Pointer
	dst.S_Slice += src.S_Slice
	dst.S_Struct += src.S_Struct
	dst.S_UnsafePointer += src.S_UnsafePointer
	dst.TagC += src.TagC
	dst.T_OmitEmpty += src.T_OmitEmpty
	dst.T_OmitZero += src.T_OmitZero
	dst.T_Ingored += src.T_Ingored
	dst.T_Named += src.T_Named
	dst.T_String += src.T_String
}

func getStructStats(st *ast.StructType, stats *JsonStats) {
	// At the moment, only count values which include a json struct tag
	count := false
	temp_stats := JsonStats{}

	for _, field := range st.Fields.List {
		switch f := field.Type.(type) {
		case *ast.Ident:
			switch f.String() {
			case "bool":
				temp_stats.S_Bool += 1
			case "int":
				temp_stats.S_Int += 1
			case "int8":
				temp_stats.S_Int8 += 1
			case "int16":
				temp_stats.S_Int16 += 1
			case "int32":
				temp_stats.S_Int32 += 1
			case "int64":
				temp_stats.S_Int64 += 1
			case "uint":
				temp_stats.S_Uint += 1
			case "uint8":
				temp_stats.S_Uint8 += 1
			case "uint16":
				temp_stats.S_Uint16 += 1
			case "uint32":
				temp_stats.S_Uint32 += 1
			case "uint64":
				temp_stats.S_Uint64 += 1
			case "uintptr":
				temp_stats.S_Uintptr += 1
			case "float32":
				temp_stats.S_Float32 += 1
			case "float64":
				temp_stats.S_Float64 += 1
			case "complex64":
				temp_stats.S_Complex64 += 1
			case "complex128":
				temp_stats.S_Complex128 += 1
			default:
				// Assume that unknown identifiers are structs?
				temp_stats.S_Struct += 1
			}
			temp_stats.S_Field += 1
		case *ast.StarExpr:
		case *ast.MapType:
		case *ast.ArrayType:
		case *ast.ChanType:
		case *ast.FuncType:
		case *ast.InterfaceType:
		case *ast.StructType:
		case *ast.SelectorExpr:
		}
	}

	if count {
		mergeStats(stats, &temp_stats)
	}
}

func GetStructStatsFromFile(filePath string) (structs []string, err error) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, filePath, nil, 0)
	if err != nil {
		return
	}

	for _, decl := range f.Decls {

		gen, ok := decl.(*ast.GenDecl)
		// Structs are type declarations
		if !ok || gen.Tok != token.TYPE {
			continue
		}

		for _, spec := range gen.Specs {
			ts, ok := spec.(*ast.TypeSpec)
			// Filter out things like ValueSpecs
			if !ok {
				continue
			}
			// Make sure we have a struct
			ss, ok := ts.Type.(*ast.StructType)
			if !ok {
				continue
			}

			fmt.Printf("Found %s\n", ts.Name.Name)
			for _, field := range ss.Fields.List {
				fmt.Printf("field: %v Type: %v (%T) Tag: %v (%T)\n", field.Names, field.Type, field.Type, field.Tag, field.Tag)
			}
			structs = append(structs, ts.Name.Name)
		}

	}
	return
}

func ComputeStats(files []string) []byte {
	structs, err := GetStructStatsFromFile(files[0])
	if err != nil {
		log.Fatalf("Error finding struct names: %v\n", err)
	}

	fmt.Printf("%v\n", structs)
	return []byte{}
}
