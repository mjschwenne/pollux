package main

import (
	"encoding/hex"
	"fmt"
	"math"
	"strconv"
)

func encode(x uint64) []byte {
	length := uint64(math.Log2(float64(x))) / 7
	fmt.Println("Length: ", length)
	result := make([]byte, 0, length)
	for x != 0 {
		nextByte := byte(x & 0x7F)
		fmt.Println("Extracted: ", nextByte)
		x = x >> 7
		// Set continuation bit
		if x > 0 {
			nextByte = nextByte | 0x80
		}
		fmt.Println("Remaining: ", x)
		result = append(result, nextByte)
	}
	return result
}

func main() {
	fmt.Println(strconv.FormatInt(0x7F, 2))
	fmt.Println(hex.EncodeToString(encode(150)))
}
