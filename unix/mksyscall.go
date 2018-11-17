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
	"go/parser"
	"go/token"
	"io"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
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

	printTraceFlag = flag.Bool("trace", false, "generate print statement after every syscall")
)

func trim(s string) string {
	return strings.Trim(s, " \t")
}

var packageName string

func packagename() string {
	return packageName
}

func syscalldot() string {
	if packageName == "syscall" || packageName == "unix" {
		return ""
	}
	return "syscall."
}

// Param is function parameter
type Param struct {
	Name      string
	Type      string
	fn        *Fn
	tmpVarIdx int
}

// tmpVar returns temp variable name that will be used to represent p during syscall.
func (p *Param) tmpVar() string {
	if p.tmpVarIdx < 0 {
		p.tmpVarIdx = p.fn.curTmpVarIdx
		p.fn.curTmpVarIdx++
	}
	return fmt.Sprintf("_p%d", p.tmpVarIdx)
}

// BoolTmpVarCode returns source code for bool temp variable.
func (p *Param) BoolTmpVarCode() string {
	const code = `var %s uint32
	if %s {
		%s = 1
	} else {
		%s = 0
	}`
	tmp := p.tmpVar()
	return fmt.Sprintf(code, tmp, p.Name, tmp, tmp)
}

// SliceTmpVarCode returns source code for slice temp variable.
func (p *Param) SliceTmpVarCode() string {
	const code = `var %s *%s
	if len(%s) > 0 {
		%s = &%s[0]
	}`
	tmp := p.tmpVar()
	return fmt.Sprintf(code, tmp, p.Type[2:], p.Name, tmp, p.Name)
}

// StringTmpVarCode returns source code for string temp variable.
func (p *Param) StringTmpVarCode() string {
	errvar := p.fn.Rets.ErrorVarName()
	if errvar == "" {
		errvar = "_"
	}
	tmp := p.tmpVar()
	const code = `var %s %s
	%s, %s = %s(%s)`
	s := fmt.Sprintf(code, tmp, p.fn.StrconvType(), tmp, errvar, p.fn.StrconvFunc(), p.Name)
	if errvar == "-" {
		return s
	}
	const morecode = `
	if %s != nil {
		return
	}`
	return s + fmt.Sprintf(morecode, errvar)
}

// TmpVarCode returns source code for temp variable.
func (p *Param) TmpVarCode() string {
	switch {
	case p.Type == "bool":
		return p.BoolTmpVarCode()
	case strings.HasPrefix(p.Type, "[]"):
		return p.SliceTmpVarCode()
	default:
		return ""
	}
}

// TmpVarHelperCode returns source code for helper's temp variable.
func (p *Param) TmpVarHelperCode() string {
	if p.Type != "string" {
		return ""
	}
	return p.StringTmpVarCode()
}

// SyscallArgList returns source code fragments representing p parameter
// in syscall. Slices are translated into 2 syscall parameters: pointer to
// the first element and length.
func (p *Param) SyscallArgList() []string {
	originalType := p.Type
	t := p.HelperType()
	var s string
	switch {
	case t[0] == '*' && originalType == "string":
		s = fmt.Sprintf("unsafe.Pointer(%s)", p.tmpVar())
	case t[0] == '*' && originalType != "string":
		s = fmt.Sprintf("unsafe.Pointer(%s)", p.Name)
	case t == "bool":
		s = p.tmpVar()
	case strings.HasPrefix(t, "[]"):
		return []string{
			fmt.Sprintf("uintptr(unsafe.Pointer(%s))", p.tmpVar()),
			fmt.Sprintf("uintptr(len(%s))", p.Name),
		}
	default:
		s = p.Name
	}
	return []string{fmt.Sprintf("uintptr(%s)", s)}
}

// IsError determines if p parameter is used to return error.
func (p *Param) IsError() bool {
	return p.Name == "err" && p.Type == "error"
}

// HelperType returns type of parameter p used in helper function.
func (p *Param) HelperType() string {
	if p.Type == "string" {
		return p.fn.StrconvType()
	}
	return p.Type
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

// Rets describes function return parameters.
type Rets struct {
	Name         string
	Type         string
	ReturnsError bool
	FailCond     string
}

// ErrorVarName returns error variable name for r.
func (r *Rets) ErrorVarName() string {
	if r.ReturnsError {
		return "err"
	}
	if r.Type == "error" {
		return r.Name
	}
	return ""
}

// ToParams converts r into slice of *Param.
func (r *Rets) ToParams() []*Param {
	ps := make([]*Param, 0)
	if len(r.Name) > 0 {
		ps = append(ps, &Param{Name: r.Name, Type: r.Type})
	}
	if r.ReturnsError {
		ps = append(ps, &Param{Name: "err", Type: "error"})
	}
	return ps
}

// List returns source code of syscall return parameters.
func (r *Rets) List() string {
	s := join(r.ToParams(), func(p *Param) string { return p.Name + " " + p.Type }, ", ")
	if len(s) > 0 {
		s = "(" + s + ")"
	}
	return s
}

// PrintList returns source code of trace printing part correspondent
// to syscall return values.
func (r *Rets) PrintList() string {
	return join(r.ToParams(), func(p *Param) string { return fmt.Sprintf(`"%s=", %s, `, p.Name, p.Name) }, `", ", `)
}

// SetReturnValuesCode returns source code that accepts syscall return values.
func (r *Rets) SetReturnValuesCode() string {
	if r.Name == "" && !r.ReturnsError {
		return ""
	}
	retvar := "r0"
	if r.Name == "" {
		retvar = "r1"
	}
	errvar := "_"
	if r.ReturnsError {
		errvar = "e1"
	}
	return fmt.Sprintf("%s, _, %s := ", retvar, errvar)
}

func (r *Rets) useLongHandleErrorCode(retvar string) string {
	const code = `if e1 != 0 {
			err = errnoErr(e1)
		}`
	return fmt.Sprintf(code)
}

// SetErrorCode returns source code that sets return parameters.
func (r *Rets) SetErrorCode() string {
	const code = `if r0 != 0 {
		%s = %sErrno(r0)
	}`
	if r.Name == "" && !r.ReturnsError {
		return ""
	}
	if r.Name == "" {
		return r.useLongHandleErrorCode("r1")
	}
	if r.Type == "error" {
		return fmt.Sprintf(code, r.Name, syscalldot())
	}
	s := ""
	switch {
	case r.Type[0] == '*':
		s = fmt.Sprintf("%s = (%s)(unsafe.Pointer(r0))", r.Name, r.Type)
	case r.Type == "bool":
		s = fmt.Sprintf("%s = r0 != 0", r.Name)
	default:
		s = fmt.Sprintf("%s = %s(r0)", r.Name, r.Type)
	}
	if !r.ReturnsError {
		return s
	}
	return s + "\n\t" + r.useLongHandleErrorCode(r.Name)
}

// Fn describes syscall function.
type Fn struct {
	Name       string   // function name
	IsSysNB    bool     // false - sys, true - sysnb
	SysName    string   // SYS_NAME
	Params     []*Param // function parameters (i.e in)
	Rets       *Rets    // function return parameters (i.e out)
	PrintTrace bool
	src        string
	// TODO: get rid of this field and just use parameter index instead
	curTmpVarIdx int // insure tmp variables have uniq names
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
		Rets:       &Rets{},
		src:        s,
		PrintTrace: *printTraceFlag,
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
		r, err := extractParams(body, f)
		if err != nil {
			return nil, err
		}
		switch len(r) {
		case 0:
		case 1:
			if r[0].IsError() {
				f.Rets.ReturnsError = true
			} else {
				f.Rets.Name = r[0].Name
				f.Rets.Type = r[0].Type
			}
		case 2:
			if !r[1].IsError() {
				return nil, errors.New("Only last windows error is allowed as second return value in \"" + f.src + "\"")
			}
			f.Rets.ReturnsError = true
			f.Rets.Name = r[0].Name
			f.Rets.Type = r[0].Type
		default:
			return nil, errors.New("Too many return values in \"" + f.src + "\"")
		}
	}
	// fail condition
	_, body, s, found = extractSection(s, '[', ']')
	if found {
		f.Rets.FailCond = body
	}
	return f, nil
}

// ParamList returns source code for function f parameters.
func (f *Fn) ParamList() string {
	return join(f.Params, func(p *Param) string { return p.Name + " " + p.Type }, ", ")
}

// HelperParamList returns source code for helper function f parameters.
func (f *Fn) HelperParamList() string {
	return join(f.Params, func(p *Param) string { return p.Name + " " + p.HelperType() }, ", ")
}

// ParamPrintList returns source code of trace printing part correspondent
// to syscall input parameters.
func (f *Fn) ParamPrintList() string {
	return join(f.Params, func(p *Param) string { return fmt.Sprintf(`"%s=", %s, `, p.Name, p.Name) }, `", ", `)
}

// ParamCount return number of syscall parameters for function f.
func (f *Fn) ParamCount() int {
	n := 0
	for _, p := range f.Params {
		n += len(p.SyscallArgList())
	}
	return n
}

// SyscallParamCount determines which version of Syscall/Syscall6/Syscall9/...
// to use. It returns parameter count for correspondent SyscallX function.
func (f *Fn) SyscallParamCount() int {
	n := f.ParamCount()
	switch {
	case n <= 3:
		return 3
	case n <= 6:
		return 6
	case n <= 9:
		return 9
	case n <= 12:
		return 12
	case n <= 15:
		return 15
	default:
		panic("too many arguments to system call")
	}
}

// Syscall determines which SyscallX function to use for function f.
func (f *Fn) Syscall() string {
	c := f.SyscallParamCount()
	if c == 3 {
		return syscalldot() + "Syscall"
	}
	return syscalldot() + "Syscall" + strconv.Itoa(c)
}

// SyscallParamList returns source code for SyscallX parameters for function f.
func (f *Fn) SyscallParamList() string {
	a := make([]string, 0)
	for _, p := range f.Params {
		a = append(a, p.SyscallArgList()...)
	}
	for len(a) < f.SyscallParamCount() {
		a = append(a, "0")
	}
	return strings.Join(a, ", ")
}

// HelperCallParamList returns source code of call into function f helper.
func (f *Fn) HelperCallParamList() string {
	a := make([]string, 0, len(f.Params))
	for _, p := range f.Params {
		s := p.Name
		if p.Type == "string" {
			s = p.tmpVar()
		}
		a = append(a, s)
	}
	return strings.Join(a, ", ")
}

// StrconvFunc returns name of Go string to OS string function for f.
func (f *Fn) StrconvFunc() string {
	return syscalldot() + "BytePtrFromString"
}

// StrconvType returns Go type name used for OS string for f.
func (f *Fn) StrconvType() string {
	return "*byte"
}

// HasStringParam is true, if f has at least one string parameter.
// Otherwise it is false.
func (f *Fn) HasStringParam() bool {
	for _, p := range f.Params {
		if p.Type == "string" {
			return true
		}
	}
	return true
}

// HelperName returns name of function f helper.
func (f *Fn) HelperName() string {
	if !f.HasStringParam() {
		return f.Name
	}
	return "_" + f.Name
}

// Source files and functions.
type Source struct {
	Funcs           []*Fn
	Files           []string
	StdLibImports   []string
	ExternalImports []string
}

func (src *Source) Import(pkg string) {
	src.StdLibImports = append(src.StdLibImports, pkg)
	sort.Strings(src.StdLibImports)
}

func (src *Source) ExternalImport(pkg string) {
	src.ExternalImports = append(src.ExternalImports, pkg)
	sort.Strings(src.ExternalImports)
}

// ParseFiles parses files listed in fs and extracts all syscall
// functions listed in sys comments. It returns source files
// and functions collection *Source if successful.
func ParseFiles(fs []string) (*Source, error) {
	src := &Source{
		Funcs: make([]*Fn, 0),
		Files: make([]string, 0),
		StdLibImports: []string{
			"unsafe",
		},
		ExternalImports: make([]string, 0),
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

	// get package name
	fset := token.NewFileSet()
	_, err = file.Seek(0, 0)
	if err != nil {
		return err
	}
	pkg, err := parser.ParseFile(fset, "", file, parser.PackageClauseOnly)
	if err != nil {
		return err
	}
	packageName = pkg.Name.Name

	return nil
}

// IsStdRepo reports whether src is part of standard library.
func (src *Source) IsStdRepo() (bool, error) {
	if len(src.Files) == 0 {
		return false, errors.New("no input files provided")
	}
	abspath, err := filepath.Abs(src.Files[0])
	if err != nil {
		return false, err
	}
	goroot := runtime.GOROOT()
	if runtime.GOOS == "windows" {
		abspath = strings.ToLower(abspath)
		goroot = strings.ToLower(goroot)
	}
	sep := string(os.PathSeparator)
	if !strings.HasSuffix(goroot, sep) {
		goroot += sep
	}
	return strings.HasPrefix(abspath, goroot), nil
}

// Generate output source file from a source set src.
func (src *Source) Generate(w io.Writer) error {
	if packageName != "syscall" {
		src.Import("syscall")
	}
	funcMap := template.FuncMap{
		"packagename": packagename,
		"syscalldot":  syscalldot,
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
	flag.PrintDefaults()
	os.Exit(1)
}

func main() {
	flag.Usage = usage
	flag.Parse()
	if len(flag.Args()) <= 0 {
		fmt.Fprintf(os.Stderr, "no files to parse provided\n")
		usage()
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

// TODO: use println instead to print in the following template
const srcTemplate = `

{{define "main"}}// Code generated by the command above; see README.md. DO NOT EDIT.

package {{packagename}}

import (
{{range .StdLibImports}}"{{.}}"
{{end}}

{{range .ExternalImports}}"{{.}}"
{{end}}
)

var _ syscall.Errno
{{range .Funcs}}
// THIS FILE IS GENERATED BY THE COMMAND AT THE TOP; DO NOT EDIT

{{if .HasStringParam}}{{template "helperbody" .}}{{end}}{{template "funcbody" .}}{{end}}
{{end}}

{{/* help functions */}}

{{define "helperbody"}}
func {{.Name}}({{.ParamList}}) {{template "results" .}}{
{{template "helpertmpvars" .}}	
{{end}}

{{define "funcbody"}}
{{template "tmpvars" .}} {{template "syscall" .}}
{{template "seterror" .}}	return
}
{{end}}

{{define "helpertmpvars"}}{{range .Params}}{{if .TmpVarHelperCode}}	{{.TmpVarHelperCode}}
{{end}}{{end}}{{end}}

{{define "tmpvars"}}{{range .Params}}{{if .TmpVarCode}}	{{.TmpVarCode}}
{{end}}{{end}}{{end}}

{{define "results"}}{{if .Rets.List}}{{.Rets.List}} {{end}}{{end}}

{{define "syscall"}}{{.Rets.SetReturnValuesCode}}{{.Syscall}}({{.SysName}}, {{.SyscallParamList}}){{end}}

{{define "seterror"}}{{if .Rets.SetErrorCode}}	{{.Rets.SetErrorCode}}
{{end}}{{end}}
`
