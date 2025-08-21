#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <stdio.h>
#include <dlfcn.h>
#include "svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

/* VCS error reporting routine */
extern void vcsMsgReport1(const char *, const char *, int, void *, void*, const char *);

#ifndef _VC_TYPES_
#define _VC_TYPES_
/* common definitions shared with DirectC.h */

typedef unsigned int U;
typedef unsigned char UB;
typedef unsigned char scalar;
typedef struct { U c; U d;} vec32;

#define scalar_0 0
#define scalar_1 1
#define scalar_z 2
#define scalar_x 3

extern long long int ConvUP2LLI(U* a);
extern void ConvLLI2UP(long long int a1, U* a2);
extern long long int GetLLIresult();
extern void StoreLLIresult(const unsigned int* data);
typedef struct VeriC_Descriptor *vc_handle;

#ifndef SV_3_COMPATIBILITY
#define SV_STRING const char*
#else
#define SV_STRING char*
#endif

#endif /* _VC_TYPES_ */

#ifndef _VC_STRUCT_TYPE_rsrc_msg_struct_
#define _VC_STRUCT_TYPE_rsrc_msg_struct_
typedef struct _vcs_dpi_rsrc_msg_struct	rsrc_msg_struct;
#endif

#ifndef _VC_STRUCT_TYPE_rsrc_msg_struct_
#define _VC_STRUCT_TYPE_rsrc_msg_struct_
struct	_vcs_dpi_rsrc_msg_struct	{
	SV_STRING	scope_name;
	SV_STRING	field_name;
	SV_STRING	type_name;
	SV_STRING	action;
	SV_STRING	accessor;
	SV_STRING	resource;
};

#endif


#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_check_path
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_check_path
__attribute__((weak)) int uvm_hdl_check_path(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1)) dlsym(RTLD_NEXT, "uvm_hdl_check_path");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_check_path");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_check_path */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_deposit
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_deposit
__attribute__((weak)) int uvm_hdl_deposit(/* INPUT */const char* A_1, const /* INPUT */svLogicVecVal *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, const /* INPUT */svLogicVecVal *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, const svLogicVecVal* A_2)) dlsym(RTLD_NEXT, "uvm_hdl_deposit");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_deposit");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_deposit */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_force
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_force
__attribute__((weak)) int uvm_hdl_force(/* INPUT */const char* A_1, const /* INPUT */svLogicVecVal *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, const /* INPUT */svLogicVecVal *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, const svLogicVecVal* A_2)) dlsym(RTLD_NEXT, "uvm_hdl_force");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_force");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_force */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_release_and_read
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_release_and_read
__attribute__((weak)) int uvm_hdl_release_and_read(/* INPUT */const char* A_1, /* INOUT */svLogicVecVal *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INOUT */svLogicVecVal *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, svLogicVecVal* A_2)) dlsym(RTLD_NEXT, "uvm_hdl_release_and_read");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_release_and_read");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_release_and_read */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_release
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_release
__attribute__((weak)) int uvm_hdl_release(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1)) dlsym(RTLD_NEXT, "uvm_hdl_release");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_release");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_release */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_read
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_read
__attribute__((weak)) int uvm_hdl_read(/* INPUT */const char* A_1, /* OUTPUT */svLogicVecVal *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */svLogicVecVal *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, svLogicVecVal* A_2)) dlsym(RTLD_NEXT, "uvm_hdl_read");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_read");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_read */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_hdl_read_string
#define __VCS_IMPORT_DPI_STUB_uvm_hdl_read_string
__attribute__((weak)) SV_STRING uvm_hdl_read_string(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1)) dlsym(RTLD_NEXT, "uvm_hdl_read_string");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_hdl_read_string");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_hdl_read_string */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_memory_load
#define __VCS_IMPORT_DPI_STUB_uvm_memory_load
__attribute__((weak)) int uvm_memory_load(/* INPUT */const char* A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5, /* INPUT */const char* A_6, /* INPUT */const char* A_7)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5, /* INPUT */const char* A_6, /* INPUT */const char* A_7) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, const char* A_2, const char* A_3, const char* A_4, const char* A_5, const char* A_6, const char* A_7)) dlsym(RTLD_NEXT, "uvm_memory_load");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6, A_7);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_memory_load");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_memory_load */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_get_next_arg_c
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_get_next_arg_c
__attribute__((weak)) SV_STRING uvm_dpi_get_next_arg_c(/* INPUT */int A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */int A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(int A_1)) dlsym(RTLD_NEXT, "uvm_dpi_get_next_arg_c");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_get_next_arg_c");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_get_next_arg_c */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_name_c
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_name_c
__attribute__((weak)) SV_STRING uvm_dpi_get_tool_name_c()
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)() = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)()) dlsym(RTLD_NEXT, "uvm_dpi_get_tool_name_c");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_();
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_get_tool_name_c");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_name_c */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_version_c
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_version_c
__attribute__((weak)) SV_STRING uvm_dpi_get_tool_version_c()
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)() = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)()) dlsym(RTLD_NEXT, "uvm_dpi_get_tool_version_c");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_();
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_get_tool_version_c");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_get_tool_version_c */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_regcomp
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_regcomp
__attribute__((weak)) void* uvm_dpi_regcomp(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void* (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void* (*)(const char* A_1)) dlsym(RTLD_NEXT, "uvm_dpi_regcomp");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_regcomp");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_regcomp */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_regexec
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_regexec
__attribute__((weak)) int uvm_dpi_regexec(/* INPUT */void* A_1, /* INPUT */const char* A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */void* A_1, /* INPUT */const char* A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(void* A_1, const char* A_2)) dlsym(RTLD_NEXT, "uvm_dpi_regexec");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_regexec");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_regexec */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dpi_regfree
#define __VCS_IMPORT_DPI_STUB_uvm_dpi_regfree
__attribute__((weak)) void uvm_dpi_regfree(/* INPUT */void* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* INPUT */void* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(void* A_1)) dlsym(RTLD_NEXT, "uvm_dpi_regfree");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dpi_regfree");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dpi_regfree */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_re_match
#define __VCS_IMPORT_DPI_STUB_uvm_re_match
__attribute__((weak)) int uvm_re_match(/* INPUT */const char* A_1, /* INPUT */const char* A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INPUT */const char* A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, const char* A_2)) dlsym(RTLD_NEXT, "uvm_re_match");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_re_match");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_re_match */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_dump_re_cache
#define __VCS_IMPORT_DPI_STUB_uvm_dump_re_cache
__attribute__((weak)) void uvm_dump_re_cache()
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)() = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)()) dlsym(RTLD_NEXT, "uvm_dump_re_cache");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_();
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_dump_re_cache");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_dump_re_cache */

#ifndef __VCS_IMPORT_DPI_STUB_uvm_glob_to_re
#define __VCS_IMPORT_DPI_STUB_uvm_glob_to_re
__attribute__((weak)) SV_STRING uvm_glob_to_re(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1)) dlsym(RTLD_NEXT, "uvm_glob_to_re");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "uvm_glob_to_re");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_uvm_glob_to_re */

#ifndef __VCS_IMPORT_DPI_STUB_parse_rsrc_msg
#define __VCS_IMPORT_DPI_STUB_parse_rsrc_msg
__attribute__((weak)) int parse_rsrc_msg(/* INPUT */const char* A_1, /* OUTPUT */rsrc_msg_struct *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */rsrc_msg_struct *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, rsrc_msg_struct* A_2)) dlsym(RTLD_NEXT, "parse_rsrc_msg");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "parse_rsrc_msg");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_parse_rsrc_msg */

#ifndef __VCS_IMPORT_DPI_STUB_parse_phase_msg_by_chandle
#define __VCS_IMPORT_DPI_STUB_parse_phase_msg_by_chandle
__attribute__((weak)) int parse_phase_msg_by_chandle(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2, /* OUTPUT */void* *A_3, /* OUTPUT */void* *A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2, /* OUTPUT */void* *A_3, /* OUTPUT */void* *A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, void** A_2, void** A_3, void** A_4)) dlsym(RTLD_NEXT, "parse_phase_msg_by_chandle");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "parse_phase_msg_by_chandle");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_parse_phase_msg_by_chandle */

#ifndef __VCS_IMPORT_DPI_STUB_find_substr_by_C
#define __VCS_IMPORT_DPI_STUB_find_substr_by_C
__attribute__((weak)) int find_substr_by_C(/* INPUT */const char* A_1, /* INPUT */const char* A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INPUT */const char* A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, const char* A_2)) dlsym(RTLD_NEXT, "find_substr_by_C");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "find_substr_by_C");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_find_substr_by_C */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dump_resource_value
#define __VCS_IMPORT_DPI_STUB_verdi_dump_resource_value
__attribute__((weak)) SV_STRING verdi_dump_resource_value(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1, void** A_2)) dlsym(RTLD_NEXT, "verdi_dump_resource_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dump_resource_value");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dump_resource_value */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dump_component_interface
#define __VCS_IMPORT_DPI_STUB_verdi_dump_component_interface
__attribute__((weak)) int verdi_dump_component_interface(/* INPUT */const char* A_1, /* INPUT */int A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INPUT */int A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(const char* A_1, int A_2)) dlsym(RTLD_NEXT, "verdi_dump_component_interface");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dump_component_interface");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dump_component_interface */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_upper_scope
#define __VCS_IMPORT_DPI_STUB_verdi_upper_scope
__attribute__((weak)) SV_STRING verdi_upper_scope(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1, void** A_2)) dlsym(RTLD_NEXT, "verdi_upper_scope");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_upper_scope");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_upper_scope */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dpi_get_c_string_by_chandle
#define __VCS_IMPORT_DPI_STUB_verdi_dpi_get_c_string_by_chandle
__attribute__((weak)) SV_STRING verdi_dpi_get_c_string_by_chandle(/* INPUT */void* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */void* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(void* A_1)) dlsym(RTLD_NEXT, "verdi_dpi_get_c_string_by_chandle");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dpi_get_c_string_by_chandle");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dpi_get_c_string_by_chandle */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dpi_free_c_string_by_chandle
#define __VCS_IMPORT_DPI_STUB_verdi_dpi_free_c_string_by_chandle
__attribute__((weak)) void verdi_dpi_free_c_string_by_chandle(/* INPUT */void* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* INPUT */void* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(void* A_1)) dlsym(RTLD_NEXT, "verdi_dpi_free_c_string_by_chandle");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dpi_free_c_string_by_chandle");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dpi_free_c_string_by_chandle */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_comp_hier
#define __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_comp_hier
__attribute__((weak)) void verdi_dhier_interface_by_comp_hier(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(const char* A_1)) dlsym(RTLD_NEXT, "verdi_dhier_interface_by_comp_hier");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dhier_interface_by_comp_hier");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_comp_hier */

#ifndef __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_classdefn
#define __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_classdefn
__attribute__((weak)) void verdi_dhier_interface_by_classdefn(/* INPUT */const char* A_1)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* INPUT */const char* A_1) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(const char* A_1)) dlsym(RTLD_NEXT, "verdi_dhier_interface_by_classdefn");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "verdi_dhier_interface_by_classdefn");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_verdi_dhier_interface_by_classdefn */

#ifndef __VCS_IMPORT_DPI_STUB_retrieve_reg_def_class
#define __VCS_IMPORT_DPI_STUB_retrieve_reg_def_class
__attribute__((weak)) void retrieve_reg_def_class(/* INPUT */const char* A_1, /* INPUT */int A_2, /* INPUT */int A_3)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* INPUT */int A_2, /* INPUT */int A_3) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(const char* A_1, int A_2, int A_3)) dlsym(RTLD_NEXT, "retrieve_reg_def_class");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "retrieve_reg_def_class");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_retrieve_reg_def_class */

#ifndef __VCS_IMPORT_DPI_STUB_retrieve_def_class
#define __VCS_IMPORT_DPI_STUB_retrieve_def_class
__attribute__((weak)) SV_STRING retrieve_def_class(/* INPUT */const char* A_1, /* OUTPUT */int *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */int *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1, int* A_2)) dlsym(RTLD_NEXT, "retrieve_def_class");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "retrieve_def_class");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_retrieve_def_class */

#ifndef __VCS_IMPORT_DPI_STUB_record_reg_decl_name
#define __VCS_IMPORT_DPI_STUB_record_reg_decl_name
__attribute__((weak)) int record_reg_decl_name(/* INPUT */int A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* INPUT */int A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(int A_1, const char* A_2, const char* A_3, const char* A_4)) dlsym(RTLD_NEXT, "record_reg_decl_name");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "record_reg_decl_name");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_record_reg_decl_name */

#ifndef __VCS_IMPORT_DPI_STUB_check_is_sequencer
#define __VCS_IMPORT_DPI_STUB_check_is_sequencer
__attribute__((weak)) int check_is_sequencer()
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)() = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)()) dlsym(RTLD_NEXT, "check_is_sequencer");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_();
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "check_is_sequencer");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_check_is_sequencer */

#ifndef __VCS_IMPORT_DPI_STUB_remove_array_index
#define __VCS_IMPORT_DPI_STUB_remove_array_index
__attribute__((weak)) SV_STRING remove_array_index(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* INPUT */const char* A_1, /* OUTPUT */void* *A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(const char* A_1, void** A_2)) dlsym(RTLD_NEXT, "remove_array_index");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "remove_array_index");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_remove_array_index */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_logicvec_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_logicvec_attribute
__attribute__((weak)) void fsdbTransDPI_scope_add_logicvec_attribute(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, const char* A_3, const svLogicVecVal* A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_scope_add_logicvec_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_scope_add_logicvec_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_logicvec_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_int_attribute
__attribute__((weak)) void fsdbTransDPI_scope_add_int_attribute(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, const char* A_3, int A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_scope_add_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_scope_add_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_string_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_string_attribute
__attribute__((weak)) void fsdbTransDPI_scope_add_string_attribute(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, const char* A_3, const char* A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_scope_add_string_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_scope_add_string_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_string_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_real_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_real_attribute
__attribute__((weak)) void fsdbTransDPI_scope_add_real_attribute(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, const char* A_3, double A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_scope_add_real_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_scope_add_real_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_real_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_enum_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_enum_int_attribute
__attribute__((weak)) void fsdbTransDPI_scope_add_enum_int_attribute(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, const char* A_3, unsigned int A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_scope_add_enum_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_scope_add_enum_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_scope_add_enum_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_begin
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_begin
__attribute__((weak)) int fsdbTransDPI_create_stream_begin(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(int* A_1, const char* A_2, const char* A_3, const char* A_4)) dlsym(RTLD_NEXT, "fsdbTransDPI_create_stream_begin");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_create_stream_begin");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_begin */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_logicvec_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_logicvec_attribute
__attribute__((weak)) void fsdbTransDPI_define_logicvec_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, const svLogicVecVal* A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_define_logicvec_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_define_logicvec_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_logicvec_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_int_attribute
__attribute__((weak)) void fsdbTransDPI_define_int_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, int A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_define_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_define_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_string_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_string_attribute
__attribute__((weak)) void fsdbTransDPI_define_string_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, const char* A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_define_string_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_define_string_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_string_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_real_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_real_attribute
__attribute__((weak)) void fsdbTransDPI_define_real_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, double A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_define_real_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_define_real_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_real_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_enum_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_enum_int_attribute
__attribute__((weak)) void fsdbTransDPI_define_enum_int_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, unsigned int A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_define_enum_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_define_enum_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_define_enum_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_logicvec_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_logicvec_attribute
__attribute__((weak)) void fsdbTransDPI_stream_add_logicvec_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, const svLogicVecVal* A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_stream_add_logicvec_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_stream_add_logicvec_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_logicvec_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_int_attribute
__attribute__((weak)) void fsdbTransDPI_stream_add_int_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, int A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_stream_add_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_stream_add_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_string_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_string_attribute
__attribute__((weak)) void fsdbTransDPI_stream_add_string_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, const char* A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_stream_add_string_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_stream_add_string_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_string_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_real_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_real_attribute
__attribute__((weak)) void fsdbTransDPI_stream_add_real_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, double A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_stream_add_real_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_stream_add_real_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_real_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_enum_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_enum_int_attribute
__attribute__((weak)) void fsdbTransDPI_stream_add_enum_int_attribute(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3, unsigned int A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_stream_add_enum_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_stream_add_enum_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_stream_add_enum_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_end
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_end
__attribute__((weak)) void fsdbTransDPI_create_stream_end(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, int A_2, const char* A_3)) dlsym(RTLD_NEXT, "fsdbTransDPI_create_stream_end");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_create_stream_end");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_create_stream_end */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_ended_stream_id
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_ended_stream_id
__attribute__((weak)) int fsdbTransDPI_get_ended_stream_id(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static int (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (int (*)(int* A_1, const char* A_2, const char* A_3)) dlsym(RTLD_NEXT, "fsdbTransDPI_get_ended_stream_id");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_get_ended_stream_id");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_ended_stream_id */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_begin
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_begin
__attribute__((weak)) long long fsdbTransDPI_begin(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static long long (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */int A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (long long (*)(int* A_1, int A_2, const char* A_3, const char* A_4)) dlsym(RTLD_NEXT, "fsdbTransDPI_begin");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_begin");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_begin */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_set_label
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_set_label
__attribute__((weak)) void fsdbTransDPI_set_label(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const char* A_4)) dlsym(RTLD_NEXT, "fsdbTransDPI_set_label");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_set_label");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_set_label */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_tag
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_tag
__attribute__((weak)) void fsdbTransDPI_add_tag(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const char* A_4)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_tag");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_tag");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_tag */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute
__attribute__((weak)) void fsdbTransDPI_add_logicvec_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const svLogicVecVal* A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_logicvec_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_logicvec_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute
__attribute__((weak)) void fsdbTransDPI_add_bitvec_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svBitVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svBitVecVal *A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const svBitVecVal* A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_bitvec_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_bitvec_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute
__attribute__((weak)) void fsdbTransDPI_add_int_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, int A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute
__attribute__((weak)) void fsdbTransDPI_add_shortint_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */short int A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */short int A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, short int A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_shortint_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_shortint_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute
__attribute__((weak)) void fsdbTransDPI_add_longint_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */long long A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */long long A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, long long A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_longint_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_longint_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute
__attribute__((weak)) void fsdbTransDPI_add_string_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const char* A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_string_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_string_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute
__attribute__((weak)) void fsdbTransDPI_add_real_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, double A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_real_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_real_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute
__attribute__((weak)) void fsdbTransDPI_add_enum_int_attribute(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, unsigned int A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_enum_int_attribute");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_enum_int_attribute");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_logicvec_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, const /* INPUT */svLogicVecVal *A_6, /* INPUT */const char* A_7)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svLogicVecVal *A_4, /* INPUT */int A_5, const /* INPUT */svLogicVecVal *A_6, /* INPUT */const char* A_7) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const svLogicVecVal* A_4, int A_5, const svLogicVecVal* A_6, const char* A_7)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_logicvec_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6, A_7);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_logicvec_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_logicvec_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_bitvec_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svBitVecVal *A_4, /* INPUT */int A_5, const /* INPUT */svBitVecVal *A_6, /* INPUT */const char* A_7)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, const /* INPUT */svBitVecVal *A_4, /* INPUT */int A_5, const /* INPUT */svBitVecVal *A_6, /* INPUT */const char* A_7) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const svBitVecVal* A_4, int A_5, const svBitVecVal* A_6, const char* A_7)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_bitvec_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6, A_7);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_bitvec_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_bitvec_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_int_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */int A_4, /* INPUT */int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, int A_4, int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_int_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_int_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_int_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_shortint_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */short int A_4, /* INPUT */short int A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */short int A_4, /* INPUT */short int A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, short int A_4, short int A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_shortint_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_shortint_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_shortint_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_longint_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */long long A_4, /* INPUT */long long A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */long long A_4, /* INPUT */long long A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, long long A_4, long long A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_longint_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_longint_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_longint_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_string_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */const char* A_4, /* INPUT */const char* A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, const char* A_4, const char* A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_string_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_string_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_string_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_real_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */double A_5, /* INPUT */const char* A_6)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */double A_4, /* INPUT */double A_5, /* INPUT */const char* A_6) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, double A_4, double A_5, const char* A_6)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_real_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_real_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_real_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute_with_expected_value
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute_with_expected_value
__attribute__((weak)) void fsdbTransDPI_add_enum_int_attribute_with_expected_value(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */int A_6, /* INPUT */const char* A_7)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3, /* INPUT */unsigned int A_4, /* INPUT */int A_5, /* INPUT */int A_6, /* INPUT */const char* A_7) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3, unsigned int A_4, int A_5, int A_6, const char* A_7)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_enum_int_attribute_with_expected_value");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5, A_6, A_7);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_enum_int_attribute_with_expected_value");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_enum_int_attribute_with_expected_value */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_end
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_end
__attribute__((weak)) void fsdbTransDPI_end(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */long long A_2, /* INPUT */const char* A_3) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, long long A_2, const char* A_3)) dlsym(RTLD_NEXT, "fsdbTransDPI_end");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_end");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_end */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_relation
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_relation
__attribute__((weak)) void fsdbTransDPI_add_relation(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */long long A_3, /* INPUT */long long A_4, /* INPUT */const char* A_5)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static void (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */long long A_3, /* INPUT */long long A_4, /* INPUT */const char* A_5) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (void (*)(int* A_1, const char* A_2, long long A_3, long long A_4, const char* A_5)) dlsym(RTLD_NEXT, "fsdbTransDPI_add_relation");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        _vcs_dpi_fp_(A_1, A_2, A_3, A_4, A_5);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_add_relation");
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_add_relation */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_enum_id
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_enum_id
__attribute__((weak)) unsigned int fsdbTransDPI_get_enum_id(/* OUTPUT */int *A_1, /* INPUT */const char* A_2)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static unsigned int (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (unsigned int (*)(int* A_1, const char* A_2)) dlsym(RTLD_NEXT, "fsdbTransDPI_get_enum_id");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_get_enum_id");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_enum_id */

#ifndef __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_class_str
#define __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_class_str
__attribute__((weak)) SV_STRING fsdbTransDPI_get_class_str(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3)
{
    static int _vcs_dpi_stub_initialized_ = 0;
    static SV_STRING (*_vcs_dpi_fp_)(/* OUTPUT */int *A_1, /* INPUT */const char* A_2, /* INPUT */const char* A_3) = NULL;
    if (!_vcs_dpi_stub_initialized_) {
        _vcs_dpi_fp_ = (SV_STRING (*)(int* A_1, const char* A_2, const char* A_3)) dlsym(RTLD_NEXT, "fsdbTransDPI_get_class_str");
        _vcs_dpi_stub_initialized_ = 1;
    }
    if (_vcs_dpi_fp_) {
        return _vcs_dpi_fp_(A_1, A_2, A_3);
    } else {
        const char *fileName;
        int lineNumber;
        svGetCallerInfo(&fileName, &lineNumber);
        vcsMsgReport1("DPI-DIFNF", fileName, lineNumber, 0, 0, "fsdbTransDPI_get_class_str");
        return 0;
    }
}
#endif /* __VCS_IMPORT_DPI_STUB_fsdbTransDPI_get_class_str */

#ifndef __VCS_EXPORT_DPI_DUMMY_REFERENCES__
#define __VCS_EXPORT_DPI_DUMMY_REFERENCES__
/* Dummy references to those export DPI routines.
 * The symbols will be then exported, so the
 * import DPI routines in another shared
 * libraries can call.
 */
void __vcs_export_dpi_dummy_references__();
void __vcs_export_dpi_dummy_references__()
{
    extern void m__uvm_report_dpi(void);
    void (*fp0)(void) = (void (*)(void)) m__uvm_report_dpi;
    fp0 = fp0;
    extern void pli_dhier_begin_event(void);
    void (*fp1)(void) = (void (*)(void)) pli_dhier_begin_event;
    fp1 = fp1;
    extern void pli_trans_add_class_name_attr(void);
    void (*fp2)(void) = (void (*)(void)) pli_trans_add_class_name_attr;
    fp2 = fp2;
    extern void pli_trans_add_vif_attr(void);
    void (*fp3)(void) = (void (*)(void)) pli_trans_add_vif_attr;
    fp3 = fp3;
    extern void pli_dhier_set_label(void);
    void (*fp4)(void) = (void (*)(void)) pli_dhier_set_label;
    fp4 = fp4;
    extern void pli_dhier_add_attribute(void);
    void (*fp5)(void) = (void (*)(void)) pli_dhier_add_attribute;
    fp5 = fp5;
    extern void pli_dhier_add_attribute_int(void);
    void (*fp6)(void) = (void (*)(void)) pli_dhier_add_attribute_int;
    fp6 = fp6;
    extern void pli_dhier_end_event(void);
    void (*fp7)(void) = (void (*)(void)) pli_dhier_end_event;
    fp7 = fp7;
}
#endif /* __VCS_EXPORT_DPI_DUMMY_REFERENCES_ */

#ifdef __cplusplus
}
#endif

