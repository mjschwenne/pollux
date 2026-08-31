package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"maps"
	"os"
	"regexp"
	"slices"

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
- Maps are internally represented as a repeated field of a synthetic "entry" message. 
  The compiler marks that message with a map_entry option, so they are counted exactly, 
  as 'message_count_map_entry' and 'field_count_map', rather than guessed at from the 
  "Entry" suffix on the name.

  Those entries are still included in 'message_count_total', 'message_count_nested_msg',
  'field_count_repeated' and 'field_count_message', so that those keys mean what they 
  meant before the map counters existed. Subtract 'message_count_map_entry' to correct 
  the message counts. Each entry also contributes its own key and value fields, so the 
  correction to 'field_count_total' and to the per-type field counts is twice that.
- Fields explicitly marked 'optional' in the protobuf file are modeled as a singleton 
  oneof for technical reasons, so I've filtered out oneof fields starting with '_optional_'
  since this seems more artifical than the map pattern.

Imports are resolved against the directories given with -I, in the order given, exactly 
as protoc does. Files are reported under the paths given here rather than under the names 
the compiler knows them by, so that a caller can pass paths from 'find' alongside an 
import path and still find its own files in the output. A file that has no name of its 
own -- one of two copies of a schema, each under an import path of its own, where the 
name they share belongs to the other -- is reported on stderr rather than measured, 
since compiling it would silently measure that other copy.`,
	Args: cobra.MinimumNArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		paths, _ := cmd.Flags().GetStringArray("import-path")
		result := pollux_p.AnalyzeStats(args, paths)

		if out, _ := cmd.Flags().GetString("parquet"); out != "" {
			if err := result.WriteParquet(out); err != nil {
				log.Fatalf("Cannot write %s: %v\n", out, err)
			}
			fmt.Fprintf(os.Stderr, "Wrote %d file(s) to %s\n", len(result.Files), out)
		} else {
			s_json, err := json.Marshal(result.Files)
			if err != nil {
				log.Fatalf("Cannot encode statistics into JSON: %v\n", err)
			}
			fmt.Println(string(s_json))
		}

		reportFileErrors(result.Errors)
		if len(result.Files) == 0 {
			os.Exit(1)
		}
	},
}

// reportFileErrors names the files that did not compile, on stderr so that it
// never lands in the middle of the output being parsed.
func reportFileErrors(errs map[string]string) {
	for _, path := range slices.Sorted(maps.Keys(errs)) {
		fmt.Fprintf(os.Stderr, "%s: %s\n", path, errs[path])
	}
}

func init() {
	protoCmd.AddCommand(protoStatsCmd)
	protoStatsCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
	protoStatsCmd.Flags().StringArrayP("import-path", "I", nil,
		"Directory to resolve imports against, repeatable, as with protoc")
	protoStatsCmd.Flags().String("parquet", "",
		"Write the statistics to this parquet file instead of JSON on stdout")
}

var protoRecursionCmd = &cobra.Command{
	Use:   "recursion proto_file [proto_files]",
	Short: "Reports which messages in the input protobuf files are recursive",
	Long: `Determines how often the input files define recursive messages, and through 
which fields. A message is recursive when it lies on a cycle of the message reference 
graph, where there is an edge from a message to every message type it has a field of:

- A self recursive message has a field of its own type.
- A mutually recursive message reaches itself only through some other message, so it 
  sits in a cycle of two or more messages.

A message can be both. Cycles are reported as strongly connected components, so two 
messages that reach each other along several distinct paths are reported once.

The graph spans the input files and everything they import, but only messages declared 
in the input files are counted. Imports matter because a message can reach recursion 
that lives in one of them: a message with a google.protobuf.Struct field is not itself 
recursive, but it does contain recursion, and so can nest to unbounded depth. A cycle 
never spans files, since that would need a circular import, which protobuf forbids.

The same counters appear per file in the output of 'pollux proto stats'.

Two details of how the protobuf compiler represents things are worth knowing:

- Map fields are compiled to a repeated synthetic 'entry' message. Those entries are 
  not counted as messages here, and the reference goes straight to the map value type, 
  so a 'map<string, Node>' inside Node reads as Node referring to itself rather than as 
  a two message cycle through the entry.
- An extension field declared inside a message extends some other message, so the 
  reference it creates is attributed to the message being extended.

Also reported is the count of messages that merely contain recursion: those that can 
reach a recursive message, even though they are not themselves on a cycle.

As with 'pollux proto stats', imports resolve against the directories given with -I and 
the per-file counters are keyed by the paths given here.`,
	Args: cobra.MinimumNArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		paths, _ := cmd.Flags().GetStringArray("import-path")
		report := pollux_p.AnalyzeRecursion(args, paths)

		if out, _ := cmd.Flags().GetString("parquet"); out != "" {
			if err := report.WriteParquet(out); err != nil {
				log.Fatalf("Cannot write %s: %v\n", out, err)
			}
			fmt.Fprintf(os.Stderr, "Wrote %d file(s) to %s\n", len(report.Files), out)
		} else if text, _ := cmd.Flags().GetBool("text"); text {
			fmt.Print(report.Text())
		} else {
			fmt.Println(string(report.JSON()))
		}

		// Named on stderr as well, since the parquet form has no place
		// to carry them.
		reportFileErrors(report.Errors)

		// The report is printed either way: whatever did compile is
		// still worth having.
		if report.Totals.FileC == 0 {
			os.Exit(1)
		}
	},
}

func init() {
	protoCmd.AddCommand(protoRecursionCmd)
	protoRecursionCmd.PersistentFlags().BoolP("help", "h", false, "Show help message")
	protoRecursionCmd.Flags().BoolP("text", "t", false, "Print a human readable report instead of JSON")
	protoRecursionCmd.Flags().StringArrayP("import-path", "I", nil,
		"Directory to resolve imports against, repeatable, as with protoc")
	protoRecursionCmd.Flags().String("parquet", "",
		"Write the per-file counters to this parquet file instead of JSON on stdout")
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
	Use:   "stats <packages>",
	Short: "Outputs summary statistics for the input collection of Go file",
	Long: `Part of the evalution requires understanding the composition of the dataset.
This subcommand compiles the input go packages, type checks them and outputs a JSON 
summary of the package contents. Since this uses Go mechanisms to load packages, package 
names should be provided, not paths to the package (althought these are similar).

Note that this command works at the package level rather then the file levels. This is 
due to how Go structures the API to the type checker.

Some notes on how the statistics are generated:
- The statistics do no distinguish between named and anonymous structs, although in 
  theory this is possible.
- The Sum of all the field count keys is NOT the total number of fields in all the 
  JSON structs. Use 'field_count_total' for this purpose.
- Certain types are counted as "modified" types. This types count as the apporiate 
  modifed field AND the underlying type. In the case of a map, both the key and value 
  counts are incremented as well. The modified types are:
	* Arrays
	* Slices 
	* Maps 
	* Pointers
	* Channels`,
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
