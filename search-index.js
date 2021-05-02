var searchIndex = JSON.parse('{\
"pep440_parser":{"doc":"","t":[3,11,11,11,11,11,11,11,11,0,0,11,11,11,11,11,12,13,3,13,13,3,4,3,13,4,3,13,3,3,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,12,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,12,12,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,12,13,4,13,13,13,13,13,13,13,3,3,13,13,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],"n":["Error","borrow","borrow_mut","clone","clone_into","fmt","fmt","from","into","scheme","specifiers","to_owned","to_string","try_from","try_into","type_id","0","A","Alphanumeric","Alphanumeric","B","Label","LabelComponent","LocalVersion","Numeric","Pre","PublicVersion","Rc","Release","Version","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","canonicalize","check_parse","check_parse","clone","clone","clone","clone","clone","clone","clone","clone","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","cmp","cmp","cmp","cmp","cmp","cmp","cmp","cmp","deref","deref","deref_mut","deserialize","deserialize","deserialize","dev","epoch","eq","eq","eq","eq","eq","eq","eq","eq","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","from","from","from","from","from","from","from","from","from_str","from_str","from_str","hash","hash","hash","hash","hash","hash","hash","hash","into","into","into","into","into","into","into","into","into_vec","is_canonical","is_legacy","label","local_version","ne","ne","ne","ne","ne","new","new","parse","parse","parse","partial_cmp","partial_cmp","partial_cmp","partial_cmp","partial_cmp","partial_cmp","partial_cmp","partial_cmp","post","pre","release","serialize","serialize","serialize","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_string","to_string","to_string","to_string","to_string","to_string","to_string","to_string","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","version","0","ArbitraryEquality","ClauseType","CompatibleRelease","Exclusion","Greater","GreaterEqual","Less","LessEqual","Matching","Specifier","SpecifierSet","WildcardExclusion","WildcardMatching","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","clause_type","clone","clone_into","deserialize","deserialize","fmt","fmt","fmt","from","from","from","from_str","from_str","into","into","into","parse","parse","serialize","serialize","to_owned","to_string","to_string","try_from","try_from","try_from","try_into","try_into","try_into","type_id","type_id","type_id","version"],"q":["pep440_parser","","","","","","","","","","","","","","","","pep440_parser::scheme","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","pep440_parser::specifiers","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","",""],"d":["A parsing error.","","","","","","","","","Parsing the PEP 440 version scheme.","Parsing PEP 440 version specifiers.","","","","","","","","An alphanumeric local version label component.","","","A local version label.","A local version label component.","A PEP 440 local version.","","Prerelease segment.","A PEP 440 public version.","","Release segment.","Any version, either PEP 440 compliant or not.","","","","","","","","","","","","","","","","","Return a canonicalized version of this version, or <code>None</code> …","Parse a version, also returning if it was in the …","Parse a version, also returning if it was in the …","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Convert this back into a Vec of components.","Return if the version is canonical.","Return if the version is a legacy version (not PEP 440 …","","Return the local version, or <code>None</code> if it is a legacy …","","","","","","Create a new release segment.","Returns the local version label component only if the …","Parse a version, accepting non-canonical input.","Parse a version, accepting non-canonical input.","Parse a version, including legacy versions.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","A specifier clause type.","","","","","","","","A PEP 440 version specifier.","A set of comma-separated specifiers.","","","","","","","","","Returns the type of this specifier.","","","","","","","","","","","","","","","","Parse a version specifier.","Parse a specifier set.","","","","","","","","","","","","","","","Returns the version in this specifier."],"i":[0,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,2,3,0,4,3,0,0,0,4,0,0,3,0,0,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,9,7,8,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,5,6,5,7,8,9,7,7,3,5,6,4,2,7,8,9,3,3,5,5,6,6,4,4,2,2,7,7,8,8,9,9,3,5,6,4,2,7,8,9,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,5,9,9,8,9,3,4,2,7,8,5,6,7,8,9,3,5,6,4,2,7,8,9,7,7,7,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,3,5,6,4,2,7,8,9,8,10,11,0,11,11,11,11,11,11,11,0,0,11,11,12,10,11,12,10,11,12,11,11,12,10,12,10,11,12,10,11,12,10,12,10,11,12,10,12,10,11,12,10,12,10,11,12,10,11,12,10,11,12],"f":[null,[[]],[[]],[[],["error",3]],[[]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[]],[[]],null,null,[[]],[[],["string",3]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],null,null,null,null,null,null,null,null,null,null,null,null,null,null,[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["option",4]],[[["str",15]],[["error",3],["result",4]]],[[["str",15]],[["error",3],["result",4]]],[[],["pre",4]],[[],["release",3]],[[],["alphanumeric",3]],[[],["labelcomponent",4]],[[],["label",3]],[[],["publicversion",3]],[[],["localversion",3]],[[],["version",3]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["pre",4]],["ordering",4]],[[],["ordering",4]],[[],["ordering",4]],[[["labelcomponent",4]],["ordering",4]],[[["label",3]],["ordering",4]],[[],["ordering",4]],[[["localversion",3]],["ordering",4]],[[],["ordering",4]],[[]],[[]],[[]],[[],["result",4]],[[],["result",4]],[[],["result",4]],null,null,[[["pre",4]],["bool",15]],[[],["bool",15]],[[],["bool",15]],[[["labelcomponent",4]],["bool",15]],[[["label",3]],["bool",15]],[[["publicversion",3]],["bool",15]],[[["localversion",3]],["bool",15]],[[],["bool",15]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["str",15]],["result",4]],[[["str",15]],["result",4]],[[["str",15]],["result",4]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],[["vec",3],["u64",15]]],[[],["bool",15]],[[],["bool",15]],null,[[],[["option",4],["localversion",3]]],[[["pre",4]],["bool",15]],[[["labelcomponent",4]],["bool",15]],[[["label",3]],["bool",15]],[[["publicversion",3]],["bool",15]],[[["localversion",3]],["bool",15]],[[["vec",3],["u64",15]]],[[["string",3]],[["result",4],["string",3]]],[[["str",15]],[["error",3],["result",4]]],[[["str",15]],[["error",3],["result",4]]],[[["str",15]],[["error",3],["result",4]]],[[["pre",4]],[["ordering",4],["option",4]]],[[],[["ordering",4],["option",4]]],[[],[["ordering",4],["option",4]]],[[["labelcomponent",4]],[["ordering",4],["option",4]]],[[["label",3]],[["ordering",4],["option",4]]],[[],[["ordering",4],["option",4]]],[[["localversion",3]],[["ordering",4],["option",4]]],[[],[["ordering",4],["option",4]]],null,null,null,[[],["result",4]],[[],["result",4]],[[],["result",4]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["string",3]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,[[]],[[]],[[]],[[]],[[]],[[]],[[],["clausetype",4]],[[],["clausetype",4]],[[]],[[],["result",4]],[[],["result",4]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[]],[[]],[[]],[[["str",15]],["result",4]],[[["str",15]],["result",4]],[[]],[[]],[[]],[[["str",15]],[["error",3],["result",4]]],[[["str",15]],[["error",3],["result",4]]],[[],["result",4]],[[],["result",4]],[[]],[[],["string",3]],[[],["string",3]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["version",3]]],"p":[[3,"Error"],[3,"Label"],[4,"Pre"],[4,"LabelComponent"],[3,"Release"],[3,"Alphanumeric"],[3,"PublicVersion"],[3,"LocalVersion"],[3,"Version"],[3,"SpecifierSet"],[4,"ClauseType"],[3,"Specifier"]]}\
}');
if (window.initSearch) {window.initSearch(searchIndex)};