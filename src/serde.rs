macro_rules! impl_serde {
    { $type:ty } => {
        impl<'de> serde_dep::Deserialize<'de> for $type {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde_dep::Deserializer<'de>,
            {
                let s = String::deserialize(deserializer)?;
                std::str::FromStr::from_str(&s).map_err(serde_dep::de::Error::custom)
            }
        }

        impl serde_dep::Serialize for $type {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde_dep::Serializer,
            {
                serializer.serialize_str(&self.to_string())
            }
        }
    }
}

impl_serde! { crate::PublicVersion }
impl_serde! { crate::LocalVersion }
impl_serde! { crate::Specifier }
impl_serde! { crate::SpecifierSet }
