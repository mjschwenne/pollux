package main

import (
	"fmt"
	"time"
)

// Basic struct
type Person struct {
	Name string
	Age  int
}

// Struct with tags (commonly used for JSON, XML, etc.)
type User struct {
	ID        int    `json:"id,omitempty"`
	Username  string `json:"username" xml:"user"`
	Password  string `json:"-"` // Ignored in JSON
	CreatedAt time.Time
}

// Anonymous (embedded) struct
type Address struct {
	Street  string
	City    string
	Country string
}

// Struct with embedded fields (promoted fields)
type Employee struct {
	Person   // Embedded struct (promoted fields: Name, Age)
	Position string
	Address  // Embedded struct (promoted fields: Street, City, Country)
	Salary   float64
	Manager  *Employee // Pointer to self-referential struct
}

// Struct with slices and maps
type Team struct {
	Name    string
	Members []Person
	Skills  map[string]int // e.g., "Go": 5, "Python": 3
}

type App struct {
	Name   string
	Logger // Embedded interface
}

type Logger interface {
	Log(s string) error
}

// Struct with type aliases and anonymous fields
type (
	Point2D struct{ X, Y int }
	Point3D struct {
		Point2D // Anonymous field (promoted: X, Y)
		Z       int
	}
)

func main() {
	// Example usage
	user := User{
		ID:       1,
		Username: "johndoe",
		Password: "secret",
	}
	fmt.Printf("%+v\n", user)

	emp := Employee{
		Person:   Person{Name: "Alice", Age: 30},
		Position: "Developer",
		Address: Address{
			Street:  "123 Main St",
			City:    "Tech City",
			Country: "USA",
		},
		Salary: 100000,
	}
	fmt.Printf("%+v\n", emp)
}
