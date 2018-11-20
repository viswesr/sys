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
	"flag"
	"fmt"
	"os"
	"regexp"
	"strings"
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
	Name string
	Type string
}

func usage() {
	fmt.Fprintf(os.Stderr, "usage: go run mksyscall.go [-b32 | -l32] [-tags x,y] [file ...]\n")
	os.Exit(1)
}

func parseParamList(list string) []string {
	list = regexp.MustCompile(`^\s*`).ReplaceAllString(list, ``)
	list = regexp.MustCompile(`\s*$`).ReplaceAllString(list, ``)
	if list == "" {
		return []string{}
	}
	return regexp.MustCompile(`\s*,\s*`).Split(list, -1)
}

func parseParam(p string) Param {
	ps := regexp.MustCompile(`^(\S*) (\S*)$`).FindStringSubmatch(p)
	if ps == nil {
		fmt.Fprintf(os.Stderr, "malformed parameter: %s\n", p)
		os.Exit(1)
	}
	return Param{ps[1], ps[2]}
}

func main() {
	flag.Usage = usage
	flag.Parse()
	if len(flag.Args()) <= 0 {
		fmt.Fprintf(os.Stderr, "no files to parse provided\n")
		usage()
	}

	_32bit := ""
	if *b32 {
		_32bit = "big-endian"
	} else if *l32 {
		_32bit = "little-endian"
	}

	// Check that we are using the new build system if we should
	if os.Getenv("GOOS") == "linux" && os.Getenv("GOARCH") != "sparc64" {
		if os.Getenv("GOLANG_SYS_BUILD") != "docker" {
			fmt.Fprintf(os.Stderr, "In the new build system, mksyscall should not be called directly.\n")
			fmt.Fprintf(os.Stderr, "See README.md\n")
			os.Exit(1)
		}
	}

	text := ""
	for _, path := range flag.Args() {
		file, err := os.Open(path)
		if err != nil {
			fmt.Fprintf(os.Stderr, err.Error())
			os.Exit(1)
		}
		defer file.Close()

		s := bufio.NewScanner(file)
		for s.Scan() {
			t := s.Text()
			t = regexp.MustCompile(`\s+`).ReplaceAllString(t, ` `)
			t = regexp.MustCompile(`^\s+`).ReplaceAllString(t, ``)
			t = regexp.MustCompile(`\s+$`).ReplaceAllString(t, ``)
			nonblock := regexp.MustCompile(`^\/\/sysnb `).FindStringSubmatch(t)
			if regexp.MustCompile(`^\/\/sys `).FindStringSubmatch(t) == nil && nonblock == nil {
				continue
			}

			// Line must be of the form
			//	func Open(path string, mode int, perm int) (fd int, errno error)
			// Split into name, in params, out params.
			f := regexp.MustCompile(`^\/\/sys(nb)? (\w+)\(([^()]*)\)\s*(?:\(([^()]+)\))?\s*(?:=\s*((?i)SYS_[A-Z0-9_]+))?$`).FindStringSubmatch(t)
			if f == nil {
				fmt.Fprintf(os.Stderr, "malformed //sys declaration\n")
				os.Exit(1)
			}
			funct, inps, outps, sysname := f[2], f[3], f[4], f[5]

			// Split argument lists on comma.
			in := parseParamList(inps)
			out := parseParamList(outps)

			// Try in vain to keep people from editing this file.
			// The theory is that they jump into the middle of the file
			// without reading the header.
			text += "// THIS FILE IS GENERATED BY THE COMMAND AT THE TOP; DO NOT EDIT\n\n"

			// Go function header.
			out_decl := ""
			if len(out) > 0 {
				out_decl = fmt.Sprintf(" (%s)", strings.Join(out, ", "))
			}
			text += fmt.Sprintf("func %s(%s)%s {\n", funct, strings.Join(in, ", "), out_decl)

			// Check if err return available
			errvar := ""
			for _, param := range out {
				p := parseParam(param)
				if p.Type == "error" {
					errvar = p.Name
					break
				}
			}

			// Prepare arguments to Syscall.
			var args []string
			n := 0
			for _, param := range in {
				p := parseParam(param)
				if regexp.MustCompile(`^\*`).FindStringSubmatch(p.Type) != nil {
					args = append(args, "uintptr(unsafe.Pointer("+p.Name+"))")
				} else if p.Type == "string" && errvar != "" {
					text += fmt.Sprintf("\tvar _p%d *byte\n", n)
					text += fmt.Sprintf("\t_p%d, %s = BytePtrFromString(%s)\n", n, errvar, p.Name)
					text += fmt.Sprintf("\tif %s != nil {\n\t\treturn\n\t}\n", errvar)
					args = append(args, fmt.Sprintf("uintptr(unsafe.Pointer(_p%d))", n))
					n++
				} else if p.Type == "string" {
					fmt.Fprintf(os.Stderr, funct+"uses string arguments, but has no error return\n")
					text += fmt.Sprintf("\tvar _p%d *byte\n", n)
					text += fmt.Sprintf("\t_p%d, _ = BytePtrFromString(%s)\n", n, p.Name)
					args = append(args, fmt.Sprintf("uintptr(unsafe.Pointer(_p%d))", n))
					n++
				} else if regexp.MustCompile(`^\[\](.*)`).FindStringSubmatch(p.Type) != nil {
					// Convert slice into pointer, length.
					// Have to be careful not to take address of &a[0] if len == 0:
					// pass dummy pointer in that case.
					// Used to pass nil, but some OSes or simulators reject write(fd, nil, 0).
					text += fmt.Sprintf("\tvar _p%d unsafe.Pointer\n", n)
					text += fmt.Sprintf("\tif len(%s) > 0 {\n\t\t_p%d = unsafe.Pointer(&%s[0])\n\t}", p.Name, n, p.Name)
					text += fmt.Sprintf(" else {\n\t\t_p%d = unsafe.Pointer(&_zero)\n\t}\n", n)
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
					if regexp.MustCompile(`^(?i)extp(read|write)`).FindStringSubmatch(funct) == nil {
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
			if nonblock != nil {
				if errvar == "" && os.Getenv("GOOS") == "linux" {
					asm = "RawSyscallNoError"
				} else {
					asm = "RawSyscall"
				}
			} else {
				if errvar == "" && os.Getenv("GOOS") == "linux" {
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

			// System call number.
			if sysname == "" {
				sysname = "SYS_" + funct
				sysname = regexp.MustCompile(`([a-z])([A-Z])`).ReplaceAllString(sysname, `${1}_$2`)
				sysname = strings.ToUpper(sysname)
			}

			// Actual call.
			arglist := strings.Join(args, ", ")
			call := fmt.Sprintf("%s(%s, %s)", asm, sysname, arglist)

			// Assign return values.
			body := ""
			ret := []string{"_", "_", "_"}
			do_errno := false
			for i := 0; i < len(out); i++ {
				p := parseParam(out[i])
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
					if i+2 > len(out) {
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
				if errvar == "" && os.Getenv("GOOS") == "linux" {
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
			text += "\treturn\n"
			text += "}\n\n"

		}
	}
	text = strings.TrimSuffix(text, "\n\n")

	fmt.Printf(`// %s
// Code generated by the command above; see README.md. DO NOT EDIT.

// +build %s

package unix

import (
	"syscall"
	"unsafe"
)

var _ syscall.Errno

%s
`, cmdline(), buildtags(), text)

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
