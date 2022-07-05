use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, ToTokens};

use syn::{
    parse_macro_input,
    punctuated::Punctuated,
    token::{Colon2, Gt, Lt},
    AngleBracketedGenericArguments, Data, DeriveInput, Field, Fields, GenericArgument, Ident, Lit,
    Meta, NestedMeta, Path, PathArguments, PathSegment, Type, TypePath,
};

enum DeriveFieldType {
    Standard,
    Optional,
    Each(String, Type),
}

struct DeriveField {
    builder_field: Field,
    field_ident: Ident,
    field_type: Type,
    derive_field_type: DeriveFieldType,
}

fn _build_vec_dfs(
    input_fields: &std::vec::Vec<Field>,
) -> Result<std::vec::Vec<DeriveField>, TokenStream> {
    fn __transform_field_into_option_field(f: &Field) -> Field {
        Field {
            attrs: vec![],
            vis: syn::Visibility::Inherited,
            ident: std::option::Option::Some(Ident::new(
                &format!("{}", f.ident.clone().unwrap()),
                Span::call_site(),
            )),
            colon_token: std::option::Option::None,
            ty: Type::Path(TypePath {
                qself: std::option::Option::None,
                path: Path {
                    leading_colon: std::option::Option::None,
                    segments: {
                        let mut p: Punctuated<PathSegment, Colon2> = Punctuated::new();
                        p.push_value(PathSegment {
                            ident: Ident::new("std", Span::call_site()),
                            arguments: PathArguments::None,
                        });
                        p.push_punct(syn::token::Colon2::default());
                        p.push_value(PathSegment {
                            ident: Ident::new("option", Span::call_site()),
                            arguments: PathArguments::None,
                        });
                        p.push_punct(syn::token::Colon2::default());
                        p.push_value(PathSegment {
                            ident: Ident::new("Option", Span::call_site()),
                            arguments: PathArguments::AngleBracketed(
                                AngleBracketedGenericArguments {
                                    colon2_token: std::option::Option::None,
                                    lt_token: Lt::default(),
                                    args: {
                                        let mut p = Punctuated::new();
                                        p.push_value(GenericArgument::Type(f.ty.clone()));
                                        p
                                    },
                                    gt_token: Gt::default(),
                                },
                            ),
                        });
                        p
                    },
                },
            }),
        }
    }

    fn __type_unwrapper(ty: &Type, name_ty: &str) -> std::option::Option<Type> {
        let segments = if let Type::Path(type_path) = ty {
            &type_path.path.segments
        } else {
            return std::option::Option::None;
        };

        if segments.len() != 1 {
            return std::option::Option::None;
        }

        let segment = segments.first().unwrap();

        if format!("{}", segment.ident) != name_ty {
            return std::option::Option::None;
        }

        let ga = if let PathArguments::AngleBracketed(pa) = &segment.arguments {
            pa.args.first().unwrap()
        } else {
            return std::option::Option::None;
        };

        let res = if let GenericArgument::Type(ga_ty) = &ga {
            ga_ty
        } else {
            return std::option::Option::None;
        };

        std::option::Option::Some(res.clone())
    }

    enum ErrorParsing {
        BadFormat,
        EachOnNotVec,
    }

    impl ErrorParsing {
        fn to_msg(&self) -> &'static str {
            match self {
                ErrorParsing::BadFormat => "expected `builder(each = \"...\")`",
                ErrorParsing::EachOnNotVec => "each cannot be applied on another type than Vec",
            }
        }
    }

    fn __build_error<T: ToTokens>(ts: T, ep: ErrorParsing) -> TokenStream {
        syn::Error::new_spanned(ts, ep.to_msg())
            .to_compile_error()
            .into()
    }

    let mut v = std::vec::Vec::with_capacity(input_fields.len());

    for f in input_fields {
        let mut derive_field_type = DeriveFieldType::Standard;
        let mut builder_field = f.clone();
        let field_ident = Ident::new(&format!("{}", f.ident.clone().unwrap()), Span::call_site());

        let mut each_already_set = false;

        if f.attrs.len() > 1 {
            return Err(__build_error(f, ErrorParsing::BadFormat));
        }

        if f.attrs.len() == 1 {
            let attr = f.attrs.first().unwrap();
            let meta = match attr.parse_meta() {
                Ok(v) => v,
                Err(_) => return Err(__build_error(attr, ErrorParsing::BadFormat)),
            };
            let meta_list = match &meta {
                Meta::NameValue(_) | Meta::Path(_) => {
                    return Err(__build_error(meta, ErrorParsing::BadFormat))
                }
                Meta::List(meta_list) => meta_list,
            };

            if meta_list.path.segments.len() != 1
                || &format!("{}", meta_list.path.segments.first().unwrap().ident) != "builder"
                || meta_list.nested.len() != 1
            {
                return Err(__build_error(meta_list, ErrorParsing::BadFormat));
            }

            let name_value = match meta_list.nested.first().unwrap() {
                NestedMeta::Lit(_) => {
                    return Err(__build_error(meta_list, ErrorParsing::BadFormat))
                }
                NestedMeta::Meta(nested_meta) => match nested_meta {
                    Meta::List(_) | Meta::Path(_) => {
                        return Err(__build_error(meta_list, ErrorParsing::BadFormat))
                    }
                    Meta::NameValue(name_value) => name_value,
                },
            };

            if name_value.path.segments.len() != 1
                || format!("{}", name_value.path.segments.first().unwrap().ident) != "each"
            {
                return Err(__build_error(meta_list, ErrorParsing::BadFormat));
            }

            let lit_str = match &name_value.lit {
                Lit::Str(lit_str) => lit_str,
                _ => return Err(__build_error(meta_list, ErrorParsing::BadFormat)),
            };

            let name_push_setter = lit_str.value();

            let type_setter = match __type_unwrapper(&f.ty, "Vec") {
                std::option::Option::None => {
                    return Err(__build_error(f, ErrorParsing::EachOnNotVec))
                }
                std::option::Option::Some(ty) => ty,
            };

            each_already_set = true;

            derive_field_type = DeriveFieldType::Each(name_push_setter, type_setter);
        }

        let field_type = {
            if each_already_set {
                builder_field.attrs.clear();
                f.ty.clone()
            } else {
                match __type_unwrapper(&f.ty, "Option") {
                    std::option::Option::Some(ty) => {
                        derive_field_type = DeriveFieldType::Optional;
                        ty
                    }
                    std::option::Option::None => {
                        builder_field = __transform_field_into_option_field(&builder_field);
                        f.ty.clone()
                    }
                }
            }
        };

        v.push(DeriveField {
            builder_field,
            field_ident,
            field_type,
            derive_field_type,
        });
    }
    Ok(v)
}

#[proc_macro_derive(Builder, attributes(builder))]
pub fn derive(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let input = parse_macro_input!(input as DeriveInput);

    let ident = input.ident;
    let command_ident: Ident = Ident::new(&format!("{}Builder", ident), Span::call_site());

    let input_fields: std::vec::Vec<Field> = match input.data {
        Data::Enum(_) | Data::Union(_) => {
            unimplemented!("cannot implement builder on enum of union")
        }
        Data::Struct(s) => match s.fields {
            Fields::Unit | Fields::Unnamed(_) => {
                unimplemented!("cannot implement builder with unit or unnamed fields")
            }
            Fields::Named(named) => named.named.into_iter().collect(),
        },
    };

    let dfs: std::vec::Vec<DeriveField> = match _build_vec_dfs(&input_fields) {
        Ok(v) => v,
        Err(ts) => return ts,
    };

    let command_idents: std::vec::Vec<_> = dfs.iter().map(|df| &df.field_ident).collect();
    let command_fields: std::vec::Vec<_> = dfs.iter().map(|df| &df.builder_field).collect();

    let setters: std::vec::Vec<_> = dfs
        .iter()
        .map(|df| {
            let ident = &df.field_ident;
            let ty = &df.field_type;

            let (add_std_setter, add_vec_setter, opt_add_each_setter) = match &df.derive_field_type
            {
                DeriveFieldType::Each(setter_name, setter_ty) => (
                    setter_name != &format!("{}", df.field_ident),
                    true,
                    std::option::Option::Some((
                        Ident::new(setter_name, Span::call_site()),
                        setter_ty,
                    )),
                ),
                _ => (true, false, std::option::Option::None),
            };

            let mut tmp_vec = vec![];

            if let std::option::Option::Some((setter_name, setter_ty)) = opt_add_each_setter {
                tmp_vec.push(quote! {
                    pub fn #setter_name (&mut self, #setter_name: #setter_ty) -> &mut Self {
                        self.#ident.push(#setter_name);
                        self
                    }
                })
            }

            if add_std_setter {
                if add_vec_setter {
                    tmp_vec.push(quote! {
                        pub fn #ident (&mut self, #ident: #ty) -> &mut Self {
                            self.#ident = #ident;
                            self
                        }
                    });
                } else {
                    tmp_vec.push(quote! {
                        pub fn #ident (&mut self, #ident: #ty) -> &mut Self {
                            self.#ident = std::option::Option::Some(#ident);
                            self
                        }
                    });
                }
            }

            tmp_vec
        })
        .flatten()
        .collect();

    let builder_inits: std::vec::Vec<_> = dfs
        .iter()
        .map(|df| {
            let field_ident = &df.field_ident;
            match df.derive_field_type {
                DeriveFieldType::Standard | DeriveFieldType::Optional => {
                    quote! {
                        let #field_ident = std::option::Option::None;
                    }
                }
                DeriveFieldType::Each(_, _) => {
                    quote! {
                        let #field_ident = vec![];
                    }
                }
            }
        })
        .collect();

    let builder_assigns: std::vec::Vec<_> = dfs
        .iter()
        .map(|df| {
            let field_ident = &df.field_ident;
            match df.derive_field_type {
                DeriveFieldType::Standard => {
                    quote! {
                        let #field_ident = match &self.#field_ident {
                            std::option::Option::Some(v) => v.clone(),
                            std::option::Option::None => {
                                return Err(format!("Missing attr: {}.{}",
                                    stringify!(#ident),
                                    stringify!(#field_ident)).into());
                            }
                        };
                    }
                }
                DeriveFieldType::Optional | DeriveFieldType::Each(_, _) => {
                    quote! {
                        let #field_ident = self.#field_ident.clone();
                    }
                }
            }
        })
        .collect();

    let builder = quote! {
        pub fn build(&mut self) -> std::result::Result<#ident, std::boxed::Box<dyn std::error::Error>> {
            #(
                #builder_assigns
            )*

            Ok( #ident { #( #command_idents ),* } )
        }
    };

    let expanded = quote! {
        pub struct #command_ident {
            #( #command_fields ),*
        }

        impl #ident {
            fn builder() -> #command_ident {
                #(
                    #builder_inits
                )*

                #command_ident {
                    #( #command_idents ),*
                }
            }
        }

        impl #command_ident {
            #(
                #setters
            )*

            #builder
        }
    };

    TokenStream::from(expanded)
}
