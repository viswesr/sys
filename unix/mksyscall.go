// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build ignore

/*
This program reads a file containing function prototypes
(like syscall_darwin.go) and generates system call bodies.
The prototypes are marked by lines beginning with "//sys"
and read like func declarations if //sys is replaced by func, but:
	* The parameter lists must give a name for each argument.
	  This includes return parameters.
	* The parameter lists must give a type for each argument:
	  the (x, y, z int) shorthand is not allowed.
	* If the return parameter is an error number, it must be named errno.

A line beginning with //sysnb is like //sys, except that the
goroutine will not be suspended during the execution of the system
call.  This must only be used for system calls which can never
block, as otherwise the system call could cause all goroutines to
hang.

Usage:
	mksyscall [-b32 | -l32] [-tags x,y] [file ...]

The flags are:
	-output
		Specify output file name (outputs to console if blank).
*/
package main

import (
	"bufio"
	"bytes"
	"errors"
	"flag"
	"fmt"
	"go/format"
	"io"
	"io/ioutil"
	"log"
	"os"
	"regexp"
	"strings"
	"text/template"
)

var (
	b32       = flag.Bool("b32", false, "32bit big-endian")
	l32       = flag.Bool("l32", false, "32bit little-endian")
	plan9     = flag.Bool("plan9", false, "plan9")
	openbsd   = flag.Bool("openbsd", false, "openbsd")
	netbsd    = flag.Bool("netbsd", false, "netbsd")
	dragonfly = flag.Bool("dragonfly", false, "dragonfly")
	arm       = flag.Bool("arm", false, "arm")
	tags      = flag.String("tags", "", "build tags")
	filename  = flag.String("output", "", "output file name (standard output if omitted)")
)

func trim(s string) string {
	return strings.Trim(s, " \t")
}

// cmdline returns this script's commandline arguments
func cmdline() string {
	// Todo: change mksyscall.pl to go run mksyscall.go later. Kept for no git diff
	return "mksyscall.pl " + strings.Join(os.Args[1:], " ")
}

// buildtags returns build tags
func buildtags() string {
	return *tags
}

// Param is function parameter
type Param struct {
	Name      string
	Type      string
	fn        *Fn
	tmpVarIdx int
}

// join concatenates parameters ps into a string with sep separator.
// Each parameter is converted into string by applying fn to it
// before conversion.
func join(ps []*Param, fn func(*Param) string, sep string) string {
	if len(ps) == 0 {
		return ""
	}
	a := make([]string, 0)
	for _, p := range ps {
		a = append(a, fn(p))
	}
	return strings.Join(a, sep)
}

// Fn describes syscall function.
type Fn struct {
	Name         string   // function name
	IsSysNB      bool     // sys - false, sysnb - true
	SysName      string   // SYS_NAME
	Params       []*Param // function parameters (i.e in)
	Rets         []*Param // function return parameters (i.e out)
	ReturnsError bool     // If error return available
	src          string
}

// extractParams parses s to extract function parameters.
func extractParams(s string, f *Fn) ([]*Param, error) {
	s = trim(s)
	if s == "" {
		return nil, nil
	}
	a := strings.Split(s, ",")
	ps := make([]*Param, len(a))
	for i := range ps {
		s2 := trim(a[i])
		b := strings.Split(s2, " ")
		if len(b) != 2 {
			b = strings.Split(s2, "\t")
			if len(b) != 2 {
				return nil, errors.New("Could not extract function parameter from \"" + s2 + "\"")
			}
		}
		ps[i] = &Param{
			Name:      trim(b[0]),
			Type:      trim(b[1]),
			fn:        f,
			tmpVarIdx: -1,
		}
	}
	return ps, nil
}

// extractSection extracts text out of string s starting after start
// and ending just before end. found return value will indicate success,
// and prefix, body and suffix will contain correspondent parts of string s.
func extractSection(s string, start, end rune) (prefix, body, suffix string, found bool) {
	s = trim(s)
	if strings.HasPrefix(s, string(start)) {
		// no prefix
		body = s[1:]
	} else {
		a := strings.SplitN(s, string(start), 2)
		if len(a) != 2 {
			return "", "", s, false
		}
		prefix = a[0]
		body = a[1]
	}
	a := strings.SplitN(body, string(end), 2)
	if len(a) != 2 {
		return "", "", "", false
	}
	return prefix, a[0], a[1], true
}

// newFn parses string s and return created function Fn.
func newFn(s string) (*Fn, error) {
	s = trim(s)
	f := &Fn{
		src: s,
	}
	// function name and args
	prefix, body, s, found := extractSection(s, '(', ')')
	if !found || prefix == "" {
		return nil, errors.New("Could not extract function name and parameters from \"" + f.src + "\"")
	}
	f.Name = prefix
	var err error
	f.Params, err = extractParams(body, f)
	if err != nil {
		return nil, err
	}
	// return values
	_, body, s, found = extractSection(s, '(', ')')
	if found {
		f.Rets, err = extractParams(body, f)
		if err != nil {
			return nil, err
		}
		// Check if err return available
		for _, r := range f.Rets {
			if r.Type == "error" {
				f.ReturnsError = true
				if r.Name != "err" {
					return nil, errors.New("error variable name is not err  \"" + f.src + "\"")
				}
				break
			}
		}
		if len(f.Rets) > 3 {
			return nil, errors.New("Too many return values in \"" + f.src + "\"")
		}
	}
	return f, nil
}

// ParamList returns source code for function f parameters.
func (f *Fn) ParamList() string {
	return join(f.Params, func(p *Param) string { return p.Name + " " + p.Type }, ", ")
}

// RetList returns source code for function f return parameters.
func (f *Fn) RetList() string {
	if len(f.Rets) > 0 {
		return join(f.Rets, func(p *Param) string { return p.Name + " " + p.Type }, ", ")
	}
	return ""
}

func (f *Fn) FuncBody() string {
	text := ""
	var args []string
	n := 0

	_32bit := ""
	if *b32 {
		_32bit = "big-endian"
	} else if *l32 {
		_32bit = "little-endian"
	}

	for _, p := range f.Params {
		if p.Type[0] == '*' {
			args = append(args, "uintptr(unsafe.Pointer("+p.Name+"))")
		} else if p.Type == "string" && f.ReturnsError {

			text += fmt.Sprintf("\tvar _p%d *byte\n", n)
			text += fmt.Sprintf("\t_p%d, err = BytePtrFromString(%s)\n", n, p.Name)
			text += fmt.Sprintf("\tif err != nil {\n\t\treturn\n\t}\n")
			args = append(args, fmt.Sprintf("uintptr(unsafe.Pointer(_p%d))", n))
			n++
		} else if p.Type == "string" {
			fmt.Fprintf(os.Stderr, f.Name + "uses string arguments, but has no error return\n")
			text += fmt.Sprintf("\tvar _p%d *byte\n", n)
			text += fmt.Sprintf("\t_p%d, _ = BytePtrFromString(%s)\n", n, p.Name)
			args = append(args, fmt.Sprintf("uintptr(unsafe.Pointer(_p%d))", n))
			n++
		} else if strings.HasPrefix(p.Type, "[]") {
			// Convert slice into pointer, length.
			// Have to be careful not to take address of &a[0] if len == 0:
			// pass dummy pointer in that case.
			// Used to pass nil, but some OSes or simulators reject write(fd, nil, 0).
			text += fmt.Sprintf("\tvar _p%d unsafe.Pointer\n", n)
			text += fmt.Sprintf("\tif len(%s) > 0 {\n\t\t_p%d = unsafe.Pointer(&%s[0])\n\t}", p.Name, n, p.Name)
			text += fmt.Sprintf(" else {\n\t\t_p%d = unsafe.Pointer(&_zero)\n\t}", n)
			text += fmt.Sprintf("\n")
			args = append(args, fmt.Sprintf("uintptr(_p%d)", n), fmt.Sprintf("uintptr(len(%s))", p.Name))
			n++
		} else if p.Type == "int64" && (*openbsd || *netbsd) {
			args = append(args, "0")
			if _32bit == "big-endian" {
				args = append(args, fmt.Sprintf("uintptr(%s>>32)", p.Name), fmt.Sprintf("uintptr(%s)", p.Name))
			} else if _32bit == "little-endian" {
				args = append(args, fmt.Sprintf("uintptr(%s)", p.Name), fmt.Sprintf("uintptr(%s>>32)", p.Name))
			} else {
				args = append(args, fmt.Sprintf("uintptr(%s)", p.Name))
			}
		} else if p.Type == "int64" && *dragonfly {
			if !(strings.HasPrefix(strings.ToLower(f.Name), "extpread") ||
				strings.HasPrefix(strings.ToLower(f.Name), "extpwrite")) {
				args = append(args, "0")
			}
			if _32bit == "big-endian" {
				args = append(args, fmt.Sprintf("uintptr(%s>>32)", p.Name), fmt.Sprintf("uintptr(%s)", p.Name))
			} else if _32bit == "little-endian" {
				args = append(args, fmt.Sprintf("uintptr(%s)", p.Name), fmt.Sprintf("uintptr(%s>>32)", p.Name))
			} else {
				args = append(args, fmt.Sprintf("uintptr(%s)", p.Name))
			}
		} else if p.Type == "int64" && _32bit != "" {
			if len(args)%2 == 1 && *arm {
				// arm abi specifies 64-bit argument uses
				// (even, odd) pair
				args = append(args, "0")
			}
			if _32bit == "big-endian" {
				args = append(args, fmt.Sprintf("uintptr(%s>>32)", p.Name), fmt.Sprintf("uintptr(%s)", p.Name))
			} else {
				args = append(args, fmt.Sprintf("uintptr(%s)", p.Name), fmt.Sprintf("uintptr(%s>>32)", p.Name))
			}
		} else {
			args = append(args, fmt.Sprintf("uintptr(%s)", p.Name))
		}
	}

	// Determine which form to use; pad args with zeros.
	asm := "Syscall"
	if f.IsSysNB {
		if !f.ReturnsError && os.Getenv("GOOS") == "linux" {
			asm = "RawSyscallNoError"
		} else {
			asm = "RawSyscall"
		}
	} else {
		if !f.ReturnsError && os.Getenv("GOOS") == "linux" {
			asm = "SyscallNoError"
		}
	}
	if len(args) <= 3 {
		for len(args) < 3 {
			args = append(args, "0")
		}
	} else if len(args) <= 6 {
		asm += "6"
		for len(args) < 6 {
			args = append(args, "0")
		}
	} else if len(args) <= 9 {
		asm += "9"
		for len(args) < 9 {
			args = append(args, "0")
		}
	} else {
		fmt.Fprintf(os.Stderr, "too many arguments to system call\n")
	}

	// Actual call.
	arglist := strings.Join(args, ", ")
	call := fmt.Sprintf("%s(%s,%s)", asm, f.SysName, arglist)

	// Assign return values.
	body := ""
	ret := []string{"_", "_", "_"}
	do_errno := false
	for i := 0; i < len(f.Rets); i++ {
		p := f.Rets[i]
		reg := ""
		if p.Name == "err" && !*plan9 {
			reg = "e1"
			ret[2] = reg
			do_errno = true
		} else if p.Name == "err" && *plan9 {
			ret[0] = "r0"
			ret[2] = "e1"
			break
		} else {
			reg = fmt.Sprintf("r%d", i)
			ret[i] = reg
		}
		if p.Type == "bool" {
			reg = fmt.Sprintf("%s != 0", reg)
		}
		if p.Type == "int64" && _32bit != "" {
			// 64-bit number in r1:r0 or r0:r1.
			if i+2 > len(f.Rets) {
				fmt.Fprintf(os.Stderr, "not enough registers for int64 return\n")
			}
			if _32bit == "big-endian" {
				reg = fmt.Sprintf("int64(r%d)<<32 | int64(r%d)", i, i+1)
			} else {
				reg = fmt.Sprintf("int64(r%d)<<32 | int64(r%d)", i+1, i)
			}
			ret[i] = fmt.Sprintf("r%d", i)
			ret[i+1] = fmt.Sprintf("r%d", i+1)
		}
		if reg != "e1" || *plan9 {
			body += fmt.Sprintf("\t%s = %s(%s)\n", p.Name, p.Type, reg)
		}
	}

	if ret[0] == "_" && ret[1] == "_" && ret[2] == "_" {
		text += fmt.Sprintf("\t%s\n", call)
	} else {
		if !f.ReturnsError && os.Getenv("GOOS") == "linux" {
			// raw syscall without error on Linux, see golang.org/issue/22924
			text += fmt.Sprintf("\t%s, %s := %s\n", ret[0], ret[1], call)
		} else {
			text += fmt.Sprintf("\t%s, %s, %s := %s\n", ret[0], ret[1], ret[2], call)
		}
	}
	text += body

	if *plan9 && ret[2] == "e1" {
		text += "\tif int32(r0) == -1 {\n"
		text += "\t\terr = e1\n"
		text += "\t}\n"
	} else if do_errno {
		text += "\tif e1 != 0 {\n"
		text += "\t\terr = errnoErr(e1)\n"
		text += "\t}\n"
	}
	text += "\treturn"
	return text
}

// Source files and functions.
type Source struct {
	Funcs []*Fn
	Files []string
}

// ParseFiles parses files listed in fs and extracts all syscall
// functions listed in sys comments. It returns source files
// and functions collection *Source if successful.
func ParseFiles(fs []string) (*Source, error) {
	src := &Source{
		Funcs: make([]*Fn, 0),
		Files: make([]string, 0),
	}
	for _, file := range fs {
		if err := src.ParseFile(file); err != nil {
			return nil, err
		}
	}
	return src, nil
}

// ParseFile adds additional file path to a source set src.
func (src *Source) ParseFile(path string) error {
	file, err := os.Open(path)
	if err != nil {
		return err
	}
	defer file.Close()

	s := bufio.NewScanner(file)
	for s.Scan() {
		t := trim(s.Text())
		if len(t) < 7 {
			continue
		}
		if !strings.HasPrefix(t, "//sys") && !strings.HasPrefix(t, "//sysnb") {
			continue
		}
		// Check for SYS_NAME and extract
		sysname := ""
		sn := regexp.MustCompile(`\s*(?:=\s*((?i)SYS_[A-Z0-9_]+))$`).FindStringSubmatch(t)
		if sn != nil {
			t = strings.TrimSuffix(t, sn[0])
			sysname = sn[1]
		}
		// Blocking or Non-Blocking fn
		isSysNB := false
		if strings.HasPrefix(t, "//sysnb") {
			t = t[7:] //sysnb
			isSysNB = true
		} else {
			t = t[5:] //sys
		}
		if !(t[0] == ' ' || t[0] == '\t') {
			continue
		}
		f, err := newFn(t[1:])
		if err != nil {
			return err
		}
		f.IsSysNB = isSysNB
		if sysname == "" {
			sysname = "SYS_" + f.Name
			sysname = regexp.MustCompile(`([a-z])([A-Z])`).ReplaceAllString(sysname, `${1}_$2`)
			sysname = strings.ToUpper(sysname)
		}
		f.SysName = sysname
		src.Funcs = append(src.Funcs, f)
	}
	if err := s.Err(); err != nil {
		return err
	}
	src.Files = append(src.Files, path)

	_, err = file.Seek(0, 0)
	if err != nil {
		return err
	}
	if err != nil {
		return err
	}
	return nil
}

func printString(ps *string) string {
	return fmt.Sprintf("%v", *ps)
}

// Generate output source file from a source set src.
func (src *Source) Generate(w io.Writer) error {
	funcMap := template.FuncMap{
		"cmdline":     cmdline,
		"tags":        buildtags,
		"printString": printString,
	}
	t := template.Must(template.New("main").Funcs(funcMap).Parse(srcTemplate))
	err := t.Execute(w, src)
	if err != nil {
		return errors.New("Failed to execute template: " + err.Error())
	}
	return nil
}

func usage() {
	fmt.Fprintf(os.Stderr, "usage: go run mksyscall.go [-b32 | -l32] [-tags x,y] [file ...]\n")
	os.Exit(1)
}

func main() {
	flag.Usage = usage
	flag.Parse()
	if len(flag.Args()) <= 0 {
		fmt.Fprintf(os.Stderr, "no files to parse provided\n")
		usage()
	}

	// Check that we are using the new build system if we should
	if os.Getenv("GOOS") == "linux" && os.Getenv("GOARCH") != "sparc64" {
		if os.Getenv("GOLANG_SYS_BUILD") != "docker" {
			fmt.Fprintf(os.Stderr, "In the !=w build system, mksyscall should not be called directly.\n")
			fmt.Fprintf(os.Stderr, "See README.md\n")
			os.Exit(1)
		}
	}

	src, err := ParseFiles(flag.Args())
	if err != nil {
		log.Fatal(err)
	}

	var buf bytes.Buffer
	if err := src.Generate(&buf); err != nil {
		log.Fatal(err)
	}

	data, err := format.Source(buf.Bytes())
	if err != nil {
		log.Fatal(err)
	}
	if *filename == "" {
		_, err = os.Stdout.Write(data)
	} else {
		err = ioutil.WriteFile(*filename, data, 0644)
	}
	if err != nil {
		log.Fatal(err)
	}
}

const srcTemplate = `
{{define "main"}} 
// {{cmdline}}
// Code generated by the command above; see README.md. DO NOT EDIT.

// +build {{tags}}

package unix

import (
	"syscall"
	"unsafe"
)

var _ syscall.Errno

{{range .Funcs}}
// THIS FILE IS GENERATED BY THE COMMAND AT THE TOP; DO NOT EDIT
{{/* Debug Info 
// {{.Name}}|{{range .Params}}{{.Name|printString}} {{.Type|printString}}|{{end}} {{range .Rets}}{{.Name|printString}} {{.Type|printString}}|{{end}} {{.SysName}}
*/}}
func {{.Name}}({{.ParamList}}) ({{.RetList}}) {
 {{.FuncBody}} }{{end}}{{end}}
`
