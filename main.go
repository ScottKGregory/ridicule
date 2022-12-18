package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"log"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"text/template"

	"golang.org/x/tools/imports"
)

type TemplateData struct {
	Package    string
	Interfaces []*Interface
	Imports    []string
	Header     bool
}

type Interface struct {
	Name     string
	MockName string
	Funcs    []*Func
	Embedded []string
	Generics []*Param
}

type Func struct {
	Name   string
	Params []*Param
	Return []*Param
}

type Param struct {
	Name string
	Type string
}

func main() {
	in, out, header, ok := parseFlags()
	if !ok {
		fmt.Println("error: invalid flags: Invalid inputs, please provide at least the -in param")
		return
	}

	file, err := os.ReadFile(in)
	if err != nil {
		fmt.Printf("error: reading file: %s\n", err)
		return
	}

	fset := token.NewFileSet()
	parsedFile, err := parser.ParseFile(fset, "", string(file), parser.ParseComments)
	if err != nil {
		fmt.Printf("error: parsing file: %s\n", err)
		return
	}

	tempData := Parse(parsedFile)
	tempData.Header = header

	NewFileWriter().WriteMock(out, tempData)

	fmt.Printf("debug: Generated '%s' interface mocks\n", in)
}

// parseFlags reads in and out from flags and returns them.
func parseFlags() (in, out string, header, valid bool) {
	flag.StringVar(&in, "in", "", "Source file")
	flag.StringVar(&out, "out", "", "Destination file override")
	flag.BoolVar(&header, "header", false, "Set to true to include the 'do not edit' header in files")
	flag.Parse()

	if out == "" {
		out = filepath.Join(filepath.Dir(in), strings.ReplaceAll(filepath.Base(in), ".go", "_mock.go"))
	}

	if in != "" && out != "" {
		valid = true
	}
	return
}

func Parse(f *ast.File) *TemplateData {
	tempData := &TemplateData{}

	tempData.Package = f.Name.Name

	tempData.Interfaces = make([]*Interface, 0)
	ast.Inspect(f, func(n ast.Node) bool {
		switch x := n.(type) {
		// find variable declarations
		case *ast.TypeSpec:
			switch x.Type.(type) {
			// and are interfaces
			case *ast.InterfaceType:
				inter := &Interface{Name: x.Name.Name}
				if x.TypeParams != nil {
					// handle generics
					inter.Generics = []*Param{}
					for _, tp := range x.TypeParams.List {
						inter.Generics = append(inter.Generics, processExpr(tp.Type, []string{tp.Names[0].Name})...)
					}
				}

				i := x.Type.(*ast.InterfaceType)

				for _, method := range i.Methods.List {
					fun := &Func{}

					if len(method.Names) > 0 {
						fun.Name = method.Names[0].Name
					} else {
						// Assume its an embedded interface

						if ident, ok := method.Type.(*ast.Ident); ok {
							inter.Embedded = append(inter.Embedded, "Mock"+ident.Name)
						} else if sel, ok := method.Type.(*ast.SelectorExpr); ok {
							parts := strings.Split(processSelectorExpr(sel), ".")
							inter.Embedded = append(inter.Embedded, fmt.Sprintf("%s.Mock%s", parts[0], parts[1]))
						} else if star, ok := method.Type.(*ast.StarExpr); ok {
							inter.Embedded = append(inter.Embedded, "*Mock"+strings.Trim(processStarExpr(star), "*"))
						}

						continue
					}

					if funcType, ok := method.Type.(*ast.FuncType); ok {
						for _, p := range funcType.Params.List {
							params := getParams(p)
							fun.Params = append(fun.Params, params...)
						}

						if funcType.Results != nil {
							for _, r := range funcType.Results.List {
								ret := getParams(r)
								fun.Return = append(fun.Return, ret...)
							}
						}
					}
					inter.Funcs = append(inter.Funcs, fun)
				}

				tempData.Interfaces = append(tempData.Interfaces, inter)
			}
		}

		tempData.Imports = make([]string, 0)
		for _, impo := range f.Imports {
			if impo.Name != nil {
				tempData.Imports = append(tempData.Imports, fmt.Sprintf("%s %s", impo.Name.Name, impo.Path.Value))
			} else {
				tempData.Imports = append(tempData.Imports, impo.Path.Value)
			}
		}

		return true
	})

	return tempData
}

func processExpr(e ast.Expr, names []string) []*Param {
	params := make([]*Param, 0)
	switch t := e.(type) {
	case *ast.SelectorExpr:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processSelectorExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processSelectorExpr(t)})
		}
	case *ast.StarExpr:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processStarExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processStarExpr(t)})
		}
	case *ast.Ident:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: t.Name,
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: t.Name})
		}
	case *ast.MapType:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processMapExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processMapExpr(t)})
		}
	case *ast.InterfaceType:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: "interface{}",
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: "interface{}"})
		}
	case *ast.ArrayType:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processArrayExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processArrayExpr(t)})
		}
	case *ast.Ellipsis:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processEllipsisExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processEllipsisExpr(t)})
		}
	case *ast.FuncType:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processFuncExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{Type: processFuncExpr(t)})
		}
	case *ast.IndexListExpr:
		for _, n := range names {
			params = append(params, &Param{
				Name: n,
				Type: processIndexListExpr(t),
			})
		}

		if len(names) == 0 {
			params = append(params, &Param{
				Type: processIndexListExpr(t),
			})
		}
	default:
		fmt.Println(fmt.Errorf("unknown type in param: %v %s", names, reflect.TypeOf(e)))
	}

	return params
}

func getParams(p *ast.Field) []*Param {
	names := getNames(p)
	params := processExpr(p.Type, names)

	return params
}

func contains(arr []string, s string) bool {
	for _, a := range arr {
		if a == s {
			return true
		}
	}

	return false
}

func getNames(p *ast.Field) (ret []string) {
	for _, n := range p.Names {
		ret = append(ret, n.Name)
	}

	return ret
}

func processSelectorExpr(t *ast.SelectorExpr) (ret string) {
	if ident, ok := t.X.(*ast.Ident); ok {
		ret += ident.Name
	}

	return ret + "." + t.Sel.Name // context.Context
}

func processStarExpr(t *ast.StarExpr) (ret string) {
	retArr := make([]string, 0)
	for _, p := range processExpr(t.X, []string{}) {
		x := "*"
		x += p.Type
		retArr = append(retArr, x)
	}

	return strings.Join(retArr, ", ") // []string
}

func processMapExpr(t *ast.MapType) (ret string) {
	ret += "map["
	for _, p := range processExpr(t.Key, []string{}) {
		ret += p.Type
	}

	ret += "]"
	for _, p := range processExpr(t.Value, []string{}) {
		ret += p.Type
	}

	return ret // map[int]string
}

func processArrayExpr(t *ast.ArrayType) (ret string) {
	retArr := make([]string, 0)
	for _, p := range processExpr(t.Elt, []string{}) {
		x := "[]"
		x += p.Type
		retArr = append(retArr, x)
	}

	return strings.Join(retArr, ", ") // []string
}

func processEllipsisExpr(t *ast.Ellipsis) (ret string) {
	retArr := make([]string, 0)
	for _, p := range processExpr(t.Elt, []string{}) {
		str := "..."
		if p.Name != "" {
			str += p.Name + " "
		}

		str += p.Type
		retArr = append(retArr, str)
	}

	return strings.Join(retArr, ", ") // ...Message
}

func processFuncExpr(t *ast.FuncType) (ret string) {
	ret += "func("

	for _, p := range t.Params.List {
		for _, x := range getParams(p) {
			ret = fmt.Sprintf("%s%s, ", ret, x.Type)
		}
	}

	ret = strings.Trim(ret, ", ")
	ret += ")"

	if len(t.Results.List) > 1 {
		ret += "("
	}

	for _, p := range t.Results.List {
		for _, x := range getParams(p) {
			ret = fmt.Sprintf("%s%s %s, ", ret, x.Name, x.Type)
		}
	}

	ret = strings.Trim(ret, ", ")
	if len(t.Results.List) > 1 {
		ret += ")"
	}

	return ret // func(x string) (bool)
}

func processIndexListExpr(t *ast.IndexListExpr) (ret string) {
	retArr := make([]string, 0)
	for _, i := range t.Indices {
		for _, p := range processExpr(i, []string{}) {
			retArr = append(retArr, p.Type)
		}
	}

	return processExpr(t.X, []string{})[0].Type + "[" + strings.Join(retArr, ", ") + "]" // gen.Generic[name.Name, string]
}

var templateContent string = `{{- $global := . -}}
{{- if .Header }}// Code generated by 'ridicule' DO NOT EDIT.
//
// ######   #####     ######   #####  #######    ####### ######  ####### #######
// ####### #######    ####### ####### #######    ####### ####### ####### #######
// ### ### ### ###    ### ### ### ###   ###      ###     ### ###   ###     ###
// ### ### ### ###    ### ### ### ###   ###      ####### ### ###   ###     ###
// ### ### ### ###    ### ### ### ###   ###      ###     ### ###   ###     ###
// ####### #######    ### ### #######   ###      ####### ####### #######   ###
// ######   #####     ### ###  #####    ###      ####### ######  #######   ###
//
// *** DO NOT EDIT *** This file was generated by 'ridicule' *** DO NOT EDIT ***

{{end}}package {{ .Package }}

import (
	"github.com/stretchr/testify/mock"
	{{- range .Imports }}
	{{ . }}
	{{- end }}
)
{{ range $interface := .Interfaces }}
// {{ $interface.MockName }} mocks the {{ $interface.Name }} interface
type {{ $interface.MockName }}{{if len $interface.Generics }}[{{ formatParams $interface.Generics "" }}]{{end}} struct {
	mock.Mock
	{{- range .Embedded }}
	{{ . }}
	{{- end }}
}
{{- end }}
{{- range $interface := .Interfaces }}
{{- range $f := $interface.Funcs }}

// {{ $f.Name }} mocks the {{ $f.Name }} function
func (mock *{{ $interface.MockName }}{{if len $interface.Generics }}[{{ formatGenerics $interface.Generics }}]{{end}}) {{ $f.Name }}({{ formatParams $f.Params "p" }}){{ formatReturnParams $f.Return }} {
	{{- if not $f.Return }}
	mock.Called({{ formatNames $f.Params }})
	{{- else }}
	args := mock.Called({{ formatNames $f.Params }})
	{{- end }}
	{{- range $i, $r := $f.Return }}

	if args.Get({{ $i }}) != nil {
		argOk := false
		r{{ $i }}, argOk = args.Get({{ $i }}).({{ $r.Type }})
		if !argOk {
			panic("incorrect type supplied for return value [{{ $i }}], expected {{ $r.Type }}")
		}
	}
	{{- end }}{{ if $f.Return }}
	return {{ formatReturn $f.Return }}{{- end }}
}
{{- end }}
{{- end }}
`

type FileWriter struct {
	template *template.Template
}

func NewFileWriter() *FileWriter {
	funcMap := template.FuncMap{
		"add": func(x, y int) int {
			return x + y
		},
		"formatParams":       formatParams,
		"formatGenerics":     formatGenerics,
		"formatReturnParams": formatReturnParams,
		"formatNames":        formatNames,
		"formatReturn":       formatReturn,
	}
	template := template.Must(
		template.New("mock.tmpl").Funcs(funcMap).Parse(templateContent),
	)

	return &FileWriter{template}
}

func (f *FileWriter) WriteMock(outPath string, tempData *TemplateData) {
	out, err := writeMock(tempData, f, outPath)
	if err != nil {
		log.Fatalf("error writing mock: %s", err)
		return
	}

	err = os.WriteFile(outPath, out, 0o600)
	if err != nil {
		log.Fatalf("error writing file: %s", err)
		return
	}
}

func writeMock(tempData *TemplateData, file *FileWriter, outPath string) ([]byte, error) {
	for _, inter := range tempData.Interfaces {
		inter.MockName = fmt.Sprintf("Mock%s", inter.Name)
	}

	var buff bytes.Buffer
	err := file.template.Execute(&buff, tempData)
	if err != nil {
		log.Fatalf("error templating file: %s", err)
		return nil, err
	}

	out, err := imports.Process(filepath.Base(outPath), buff.Bytes(), &imports.Options{Comments: true})
	if err != nil {
		log.Printf("error tidying imports: %s", err)
		out = buff.Bytes()
	}

	return out, err
}

func formatParams(params []*Param, prefix string) string {
	formatted := make([]string, 0)
	for i, param := range params {
		p := []string{}
		if !isEmptyOrWhitespace(param.Name) {
			p = append(p, param.Name)
		} else {
			p = append(p, fmt.Sprintf("%s%d", prefix, i))
		}
		if !isEmptyOrWhitespace(param.Type) {
			p = append(p, param.Type)
		}

		formatted = append(formatted, strings.Join(p, " "))
	}

	return strings.Join(formatted, ", ")
}

func formatGenerics(params []*Param) string {
	formatted := make([]string, 0)
	for _, param := range params {
		formatted = append(formatted, param.Name)
	}

	return strings.Join(formatted, ", ")
}

func formatReturnParams(params []*Param) string {
	formatted := make([]string, 0)
	for i, param := range params {
		paramStr := []string{}
		paramStr = append(paramStr, fmt.Sprintf("r%d", i))
		if !isEmptyOrWhitespace(param.Type) {
			paramStr = append(paramStr, param.Type)
		}

		formatted = append(formatted, strings.Join(paramStr, " "))
	}

	formattedStr := strings.Join(formatted, ", ")

	if formattedStr == "" {
		return ""
	}

	if strings.Contains(formattedStr, " ") {
		return " (" + formattedStr + ")"
	}

	return " " + formattedStr
}

func formatNames(params []*Param) string {
	formatted := make([]string, 0)
	for i, param := range params {
		if param.Name != "" {
			formatted = append(formatted, param.Name)
		} else {
			formatted = append(formatted, fmt.Sprintf("p%d", i))
		}
	}

	return strings.Join(formatted, ", ")
}

func formatReturn(params []*Param) string {
	formatted := make([]string, 0)
	for i := range params {
		formatted = append(formatted, fmt.Sprintf("r%d", i))
	}

	return strings.Join(formatted, ", ")
}

func isEmptyOrWhitespace(s string) bool {
	s = strings.ReplaceAll(s, " ", "")
	return len(s) == 0
}
