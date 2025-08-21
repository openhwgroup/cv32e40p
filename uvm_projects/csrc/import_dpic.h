typedef struct _vcs_dpi_rsrc_msg_struct	rsrc_msg_struct;

struct	_vcs_dpi_rsrc_msg_struct	{
	SV_STRING	scope_name;
	SV_STRING	field_name;
	SV_STRING	type_name;
	SV_STRING	action;
	SV_STRING	accessor;
	SV_STRING	resource;
};



 extern int uvm_hdl_check_path(/* INPUT */const char* path);

 extern int uvm_hdl_deposit(/* INPUT */const char* path, const /* INPUT */svLogicVecVal *value);

 extern int uvm_hdl_force(/* INPUT */const char* path, const /* INPUT */svLogicVecVal *value);

 extern int uvm_hdl_release_and_read(/* INPUT */const char* path, /* INOUT */svLogicVecVal *value);

 extern int uvm_hdl_release(/* INPUT */const char* path);

 extern int uvm_hdl_read(/* INPUT */const char* path, /* OUTPUT */svLogicVecVal *value);

 extern SV_STRING uvm_hdl_read_string(/* INPUT */const char* path);

 extern int uvm_memory_load(/* INPUT */const char* nid, /* INPUT */const char* scope, /* INPUT */const char* fileName, /* INPUT */const char* radix, /* INPUT */const char* startaddr, /* INPUT */const char* endaddr, /* INPUT */const char* types);

 extern SV_STRING uvm_dpi_get_next_arg_c(/* INPUT */int init);

 extern SV_STRING uvm_dpi_get_tool_name_c();

 extern SV_STRING uvm_dpi_get_tool_version_c();

 extern void* uvm_dpi_regcomp(/* INPUT */const char* regex);

 extern int uvm_dpi_regexec(/* INPUT */void* preg, /* INPUT */const char* str);

 extern void uvm_dpi_regfree(/* INPUT */void* preg);

 extern int uvm_re_match(/* INPUT */const char* re, /* INPUT */const char* str);

 extern void uvm_dump_re_cache();

 extern SV_STRING uvm_glob_to_re(/* INPUT */const char* glob);

 extern int parse_rsrc_msg(/* INPUT */const char* message, /* OUTPUT */rsrc_msg_struct *_msg_fields);

 extern int parse_phase_msg_by_chandle(/* INPUT */const char* message, /* OUTPUT */void* *domain, /* OUTPUT */void* *schedule, /* OUTPUT */void* *phase);

 extern int find_substr_by_C(/* INPUT */const char* org_str, /* INPUT */const char* search_str);

 extern SV_STRING verdi_dump_resource_value(/* INPUT */const char* rsrc, /* OUTPUT */void* *rtn_str_ptr);

 extern int verdi_dump_component_interface(/* INPUT */const char* scope_name, /* INPUT */int streamId);

 extern SV_STRING verdi_upper_scope(/* INPUT */const char* inst_scope_name, /* OUTPUT */void* *upper_scope_pointer);

 extern SV_STRING verdi_dpi_get_c_string_by_chandle(/* INPUT */void* c_str_ptr);

 extern void verdi_dpi_free_c_string_by_chandle(/* INPUT */void* c_str_ptr);

 extern void verdi_dhier_interface_by_comp_hier(/* INPUT */const char* var_name);

 extern void verdi_dhier_interface_by_classdefn(/* INPUT */const char* var_name);

 extern void retrieve_reg_def_class(/* INPUT */const char* var_name, /* INPUT */int _handle, /* INPUT */int is_objid_only);

 extern SV_STRING retrieve_def_class(/* INPUT */const char* var_name, /* OUTPUT */int *objid);

 extern int record_reg_decl_name(/* INPUT */int handle, /* INPUT */const char* parent_var_name, /* INPUT */const char* var_name, /* INPUT */const char* obj_name);

 extern int check_is_sequencer();

 extern SV_STRING remove_array_index(/* INPUT */const char* name_w_ary_idx, /* OUTPUT */void* *name_c_ptr);

 extern void fsdbTransDPI_scope_add_logicvec_attribute(/* OUTPUT */int *state, /* INPUT */const char* scope_fullname, /* INPUT */const char* attribute_name, const /* INPUT */svLogicVecVal *attribute, /* INPUT */int numbit, /* INPUT */const char* options);

 extern void fsdbTransDPI_scope_add_int_attribute(/* OUTPUT */int *state, /* INPUT */const char* scope_fullname, /* INPUT */const char* attribute_name, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_scope_add_string_attribute(/* OUTPUT */int *state, /* INPUT */const char* scope_fullname, /* INPUT */const char* attribute_name, /* INPUT */const char* attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_scope_add_real_attribute(/* OUTPUT */int *state, /* INPUT */const char* scope_fullname, /* INPUT */const char* attribute_name, /* INPUT */double attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_scope_add_enum_int_attribute(/* OUTPUT */int *state, /* INPUT */const char* scope_fullname, /* INPUT */const char* attribute_name, /* INPUT */unsigned int enum_id, /* INPUT */int attribute, /* INPUT */const char* options);

 extern int fsdbTransDPI_create_stream_begin(/* OUTPUT */int *state, /* INPUT */const char* stream_fullname, /* INPUT */const char* description, /* INPUT */const char* options);

 extern void fsdbTransDPI_define_logicvec_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, const /* INPUT */svLogicVecVal *attribute, /* INPUT */int numbit, /* INPUT */const char* options);

 extern void fsdbTransDPI_define_int_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_define_string_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */const char* attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_define_real_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */double attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_define_enum_int_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */unsigned int enum_id, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_stream_add_logicvec_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, const /* INPUT */svLogicVecVal *attribute, /* INPUT */int numbit, /* INPUT */const char* options);

 extern void fsdbTransDPI_stream_add_int_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_stream_add_string_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */const char* attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_stream_add_real_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */double attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_stream_add_enum_int_attribute(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* attribute_name, /* INPUT */unsigned int enum_id, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_create_stream_end(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* options);

 extern int fsdbTransDPI_get_ended_stream_id(/* OUTPUT */int *state, /* INPUT */const char* stream_fullname, /* INPUT */const char* options);

 extern long long fsdbTransDPI_begin(/* OUTPUT */int *state, /* INPUT */int sid, /* INPUT */const char* trans_type, /* INPUT */const char* options);

 extern void fsdbTransDPI_set_label(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* label, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_tag(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* tag, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_logicvec_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, const /* INPUT */svLogicVecVal *attribute, /* INPUT */int numbit, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_bitvec_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, const /* INPUT */svBitVecVal *attribute, /* INPUT */int numbit, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_int_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_shortint_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */short int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_longint_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */long long attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_string_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */const char* attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_real_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */double attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_enum_int_attribute(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */unsigned int enum_id, /* INPUT */int attribute, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_logicvec_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, const /* INPUT */svLogicVecVal *attribute, /* INPUT */int numbit, const /* INPUT */svLogicVecVal *expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_bitvec_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, const /* INPUT */svBitVecVal *attribute, /* INPUT */int numbit, const /* INPUT */svBitVecVal *expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_int_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */int attribute, /* INPUT */int expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_shortint_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */short int attribute, /* INPUT */short int expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_longint_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */long long attribute, /* INPUT */long long expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_string_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */const char* attribute, /* INPUT */const char* expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_real_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */double attribute, /* INPUT */double expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_enum_int_attribute_with_expected_value(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* attribute_name, /* INPUT */unsigned int enum_id, /* INPUT */int attribute, /* INPUT */int expected_val, /* INPUT */const char* options);

 extern void fsdbTransDPI_end(/* OUTPUT */int *state, /* INPUT */long long tid, /* INPUT */const char* options);

 extern void fsdbTransDPI_add_relation(/* OUTPUT */int *state, /* INPUT */const char* rel_name, /* INPUT */long long master_tid, /* INPUT */long long slave_tid, /* INPUT */const char* options);

 extern unsigned int fsdbTransDPI_get_enum_id(/* OUTPUT */int *state, /* INPUT */const char* enum_var_name);

 extern SV_STRING fsdbTransDPI_get_class_str(/* OUTPUT */int *state, /* INPUT */const char* class_var_name, /* INPUT */const char* options);
