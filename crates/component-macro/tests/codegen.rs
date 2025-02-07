macro_rules! gentest {
    ($id:ident $name:tt $path:tt) => {
        mod $id {
            mod sugar {
                wasmtime::component::bindgen!(in $path);
            }
            mod async_ {
                wasmtime::component::bindgen!({
                    path: $path,
                    async: true,
                });
            }
            mod tracing {
                wasmtime::component::bindgen!({
                    path: $path,
                    tracing: true,
                    ownership: Borrowing {
                        duplicate_if_necessary: true
                    }
                });
            }
        }
    };
}

component_macro_test_helpers::foreach!(gentest);

mod with_key_and_resources {
    use anyhow::Result;
    use wasmtime::component::Resource;

    wasmtime::component::bindgen!({
        inline: "
            package demo:pkg

            interface bar {
                resource a
                resource b
            }

            world foo {
                resource a
                resource b

                import foo: interface {
                    resource a
                    resource b
                }

                import bar
            }
        ",
        with: {
            "a": MyA,
            "b": MyA,
            "foo/a": MyA,
            "foo/b": MyA,
            "demo:pkg/bar/a": MyA,
            "demo:pkg/bar/b": MyA,
        },
    });

    pub struct MyA;

    struct MyComponent;

    impl FooImports for MyComponent {}

    impl HostA for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }

    impl HostB for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }

    impl foo::Host for MyComponent {}

    impl foo::HostA for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }

    impl foo::HostB for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }

    impl demo::pkg::bar::Host for MyComponent {}

    impl demo::pkg::bar::HostA for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }

    impl demo::pkg::bar::HostB for MyComponent {
        fn drop(&mut self, _: Resource<MyA>) -> Result<()> {
            loop {}
        }
    }
}
