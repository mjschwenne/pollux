package main

import (
	"bufio"
	"fmt"
	"github.com/mjschwenne/pollux"
	"log"
	"os"
	"regexp"
)

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	scanner.Split(bufio.ScanLines)

	// Regexp checks for format changer
	format_change := `(?:[isu](?:32|64)){2}`

	var first_form string
	var second_form string
	for scanner.Scan() {
		var err error
		txt := scanner.Text()

		// Check for a change in format
		if matched, _ := regexp.MatchString(format_change, txt); matched {
			first_form = txt[:3]
			second_form = txt[3:]
			continue
		}

		// Before looping on the encoding, ensure a format has been set
		if first_form == "" || second_form == "" {
			log.Fatalln("Format specifiers aren't set!")
		}

		enc, err := pollux.Encode_varint(first_form, txt)
		if err != nil {
			log.Fatalln(err)
		}

		out, err := pollux.Decode_varint(second_form, enc)
		fmt.Println(out)
	}
}
