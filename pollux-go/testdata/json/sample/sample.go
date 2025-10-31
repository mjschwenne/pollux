package main

import "time"

// Type aliases to demonstrate resolution
type UserID int
type ProductID int64
type Email string

// Embedded struct
type Address struct {
	Street  string
	City    string
	ZipCode int
}

// Another struct for embedding
type Timestamps struct {
	CreatedAt time.Time
	UpdatedAt time.Time
}

// Main struct with various field types
type User struct {
	// Type aliases - will resolve to underlying types
	ID    UserID
	Email Email

	// Basic types
	Name    string
	Age     int
	Active  bool
	Balance float64

	// Embedded struct
	Address

	// Named struct field
	Billing Address

	// Pointer
	Manager *User

	// Slice with type alias
	Products []ProductID

	// Map with type alias
	Metadata map[string]Email

	// Complex types
	Tags      []string
	Scores    map[string]int
	CreatedAt time.Time
}

// Another struct for variety
type Product struct {
	ID          ProductID
	Name        string
	Price       float64
	InStock     bool
	Tags        []string
	Attributes  map[string]string
	ReleaseDate time.Time
}
