package pollux_proto

import (
	"errors"
	"strconv"

	varint "github.com/mjschwenne/pollux/proto"
	"google.golang.org/protobuf/proto"
)

func parse_u32(s string) (u uint32, err error) {
	u64, err := strconv.ParseUint(s, 10, 32)
	u = uint32(u64)
	return
}

func parse_i32(s string) (i int32, err error) {
	i64, err := strconv.ParseInt(s, 10, 32)
	i = int32(i64)
	return
}

func parse_u64(s string) (u uint64, err error) {
	u, err = strconv.ParseUint(s, 10, 64)
	return
}

func parse_i64(s string) (i int64, err error) {
	i, err = strconv.ParseInt(s, 10, 64)
	return
}

func Encode_varint(format string, input string) ([]byte, error) {
	switch format {
	case "u32":
		u, err := parse_u32(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.U32{
			Field: u,
		})
	case "u64":
		u, err := parse_u64(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.U64{
			Field: u,
		})
	case "i32":
		i, err := parse_i32(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.I32{
			Field: i,
		})
	case "i64":
		i, err := parse_i64(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.I64{
			Field: i,
		})
	case "s32":
		i, err := parse_i32(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.S32{
			Field: i,
		})
	case "s64":
		i, err := parse_i64(input)
		if err != nil {
			return []byte{}, err
		}
		return proto.Marshal(&varint.S64{
			Field: i,
		})
	default:
		return []byte{}, errors.New("Invalid format specifier '" + format + "'!")
	}
}

func Decode_varint(format string, enc []byte) (string, error) {
	switch format {
	case "u32":
		vint := &varint.U32{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatUint(uint64(vint.GetField()), 10), nil
	case "u64":
		vint := &varint.U64{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatUint(vint.GetField(), 10), nil
	case "i32":
		vint := &varint.I32{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatInt(int64(vint.GetField()), 10), nil
	case "i64":
		vint := &varint.I64{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatInt(vint.GetField(), 10), nil
	case "s32":
		vint := &varint.S32{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatInt(int64(vint.GetField()), 10), nil
	case "s64":
		vint := &varint.S64{}
		if err := proto.Unmarshal(enc, vint); err != nil {
			return "", err
		}
		return strconv.FormatInt(vint.GetField(), 10), nil
	default:
		return "", errors.New("Invalid format specifier '" + format + "'!")
	}
}
