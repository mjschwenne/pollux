package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"regexp"

	"github.com/mjschwenne/pollux/internal/desclib"
	pollux_j "github.com/mjschwenne/pollux/json"
	pollux_p "github.com/mjschwenne/pollux/protobuf"
	"github.com/spf13/cobra"
)

var rootCmd = &cobra.Command{
	Use:   "pollux",
	Short: "top-level access to all pollux functionality",
	Long: `Pollux is a collection of tools for analyzing and checking Protobuf files
for breaking changes. It also includes some extra functionality used as part of 
the evaluation and testing process.`,
}

func init() {
	rootCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
}

var protoCmd = &cobra.Command{
	Use:   "proto",
	Short: "Access pollux protobuf functionality",
	Long: `This subcommand accesses all of Pollux's protobuf functionality, including 
- Varint conversions
- Generating summary statistics for protobuf files 
- Checking if two protobuf files are equal`,
}

func init() {
	rootCmd.AddCommand(protoCmd)
}

var protoVarintCmd = &cobra.Command{
	Use:   "varint",
	Short: "Performs actual Protobuf varint conversion",
	Long: `Pollux uses static conversion functions to simulate the effect of casting 
between types using variable width integer conversion. This subcommand is used to test 
those functions against the protoc implementation. 

When this flag is passed, Pollux listens on stdin for integers and writes the converted 
value to stdout. This is a streaming operation, and the conversion formats can be changed
by passing two format specifiers, either i, s or u for int, sint or uint followed the bit
width. No spaces are used in the conversion format specifier.`,
	Args: cobra.NoArgs,
	Run: func(cmd *cobra.Command, args []string) {
		varint_conversion()
	},
}

func varint_conversion() {
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

		enc, err := pollux_p.Encode_varint(first_form, txt)
		if err != nil {
			log.Fatalln(err)
		}

		out, err := pollux_p.Decode_varint(second_form, enc)
		fmt.Println(out)
	}
}

func init() {
	protoCmd.AddCommand(protoVarintCmd)
	protoVarintCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
}

var protoStatsCmd = &cobra.Command{
	Use:   "stats proto_file [proto_files]",
	Short: "Outputs summary statistics for the input collection of protobuf files",
	Long: `Part of the evalution requires understanding the composition of the dataset.
Rather than parsing protobuf files in python, we decided to use go to leverage existing 
work in the unverified checker. This subcommand compiles the input protobuf files and 
outputs a JSON summary of the file contents.

Since pollux uses compiled protobuf descriptors, rather than a raw analysis of the text 
fields. In particular:

- Counts for reserved ranges and names count the number of times a message or enum uses 
  this feature, rather than the number of ranges or names reserved.
- Maps are internally represented as a repeated message type, so we can't accurately 
  count maps. In the descriptor, we do see an "Entry" suffix appended to the name, but 
  there is no way in the descriptor to know if this is a map entry or a user-defined 
  message which matches this assumption.
- Fields explicitly marked 'optional' in the protobuf file are modeled as a singleton 
  oneof for technical reasons, so I've filtered out oneof fields starting with '_optional_'
  since this seems more artifical than the map pattern.`,
	Args: cobra.MinimumNArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		fmt.Println(string(pollux_p.ComputeStats(args)))
	},
}

func init() {
	protoCmd.AddCommand(protoStatsCmd)
	protoStatsCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
}

var protoCheckCmd = &cobra.Command{
	Use:   "check old_proto_file new_proto_file",
	Short: "Checks compatibility between a protobuf file and its updated version",
	Args:  cobra.ExactArgs(2),
	Run: func(cmd *cobra.Command, args []string) {
		as, _ := desclib.CompileProtos([]string{args[0]})
		a := as[0]
		bs, _ := desclib.CompileProtos([]string{args[1]})
		b := bs[0]
		fmt.Println(desclib.FileDescEq(a, b))
	},
}

func init() {
	protoCmd.AddCommand(protoCheckCmd)
	protoCheckCmd.PersistentFlags().BoolP("strict", "s", false, "Compare for exact equality")
}

var jsonCmd = &cobra.Command{
	Use:   "json",
	Short: "Access pollux JSON + Go struct functionality",
	Long: `This subcommand accesses all of Pollux's functionality for analyzing Go structs
serialized to JSON via the encoding/json package.`,
}

func init() {
	rootCmd.AddCommand(jsonCmd)
}

var jsonStatsCmd = &cobra.Command{
	Use:   "stats",
	Short: "Outputs summary statistics for the input collection of Go file",
	Long: `Part of the evalution requires understanding the composition of the dataset.
This subcommand compiles the input protobuf files and outputs a JSON summary of the file 
contents.`,
	Args: cobra.MinimumNArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		fmt.Println(string(pollux_j.ComputeStats(args)))
	},
}

func init() {
	jsonCmd.AddCommand(jsonStatsCmd)
	jsonStatsCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
}

func main() {
	if err := rootCmd.Execute(); err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
}
