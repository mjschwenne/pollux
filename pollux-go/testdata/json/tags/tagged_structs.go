package main

import "time"

// User demonstrates common struct tags
type User struct {
	ID        int       `json:"id" db:"user_id" validate:"required"`
	Username  string    `json:"username" db:"username" validate:"required,min=3,max=20"`
	Email     string    `json:"email,omitempty" db:"email" validate:"required,email"`
	Password  string    `json:"-" db:"password_hash"`
	Age       int       `json:"age" db:"age" validate:"gte=0,lte=150"`
	Active    bool      `json:"active" db:"is_active"`
	CreatedAt time.Time `json:"created_at" db:"created_at"`
	UpdatedAt time.Time `json:"updated_at,omitempty" db:"updated_at"`
}

// Product with multiple tag formats
type Product struct {
	ID          int64   `json:"id" xml:"id" yaml:"id" bson:"_id"`
	Name        string  `json:"name" xml:"name" yaml:"name" bson:"name"`
	Description string  `json:"description,omitempty" xml:"description,omitempty" yaml:"description,omitempty"`
	Price       float64 `json:"price" xml:"price" yaml:"price" bson:"price" validate:"gt=0"`
	SKU         string  `json:"sku" xml:"sku,attr" yaml:"sku" bson:"sku" validate:"required"`
	InStock     bool    `json:"in_stock" xml:"inStock" yaml:"in_stock" bson:"in_stock"`
}

// APIResponse with nested tags
type APIResponse struct {
	Status  int         `json:"status" validate:"required"`
	Message string      `json:"message,omitempty"`
	Data    interface{} `json:"data,omitempty"`
	Error   *ErrorInfo  `json:"error,omitempty"`
}

// ErrorInfo with validation tags
type ErrorInfo struct {
	Code    string `json:"code" validate:"required"`
	Message string `json:"message" validate:"required"`
	Details string `json:"details,omitempty"`
}

// Config with different tag types
type Config struct {
	Host     string `env:"HOST" default:"localhost" validate:"required"`
	Port     int    `env:"PORT" default:"8080" validate:"min=1,max=65535"`
	Database string `env:"DATABASE" default:"mydb"`
	Debug    bool   `env:"DEBUG" default:"false"`
}
