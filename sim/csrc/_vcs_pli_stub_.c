#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <stdio.h>
#include <dlfcn.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void* VCS_dlsymLookup(const char *);
extern void vcsMsgReportNoSource1(const char *, const char*);

/* PLI routine: $fsdbDumpvars:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvars
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvars
extern void novas_call_phaseout_fsdbDumpvars(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpvars
void novas_call_phaseout_fsdbDumpvars(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpvars");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpvars");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpvars");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpvars)(int data, int reason) = novas_call_phaseout_fsdbDumpvars;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvars */

/* PLI routine: $fsdbDumpvars:misc */
#ifndef __VCS_PLI_STUB_novas_misc
#define __VCS_PLI_STUB_novas_misc
extern void novas_misc(int data, int reason, int iparam );
#pragma weak novas_misc
void novas_misc(int data, int reason, int iparam )
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason, int iparam ) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason, int iparam )) dlsym(RTLD_NEXT, "novas_misc");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason, int iparam )) VCS_dlsymLookup("novas_misc");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason, iparam );
    }
}
void (*__vcs_pli_dummy_reference_novas_misc)(int data, int reason, int iparam ) = novas_misc;
#endif /* __VCS_PLI_STUB_novas_misc */

/* PLI routine: $fsdbDumpvarsByFile:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvarsByFile
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvarsByFile
extern void novas_call_phaseout_fsdbDumpvarsByFile(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpvarsByFile
void novas_call_phaseout_fsdbDumpvarsByFile(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpvarsByFile");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpvarsByFile");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpvarsByFile");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpvarsByFile)(int data, int reason) = novas_call_phaseout_fsdbDumpvarsByFile;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpvarsByFile */

/* PLI routine: $fsdbAddRuntimeSignal:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbAddRuntimeSignal
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbAddRuntimeSignal
extern void novas_call_phaseout_fsdbAddRuntimeSignal(int data, int reason);
#pragma weak novas_call_phaseout_fsdbAddRuntimeSignal
void novas_call_phaseout_fsdbAddRuntimeSignal(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbAddRuntimeSignal");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbAddRuntimeSignal");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbAddRuntimeSignal");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbAddRuntimeSignal)(int data, int reason) = novas_call_phaseout_fsdbAddRuntimeSignal;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbAddRuntimeSignal */

/* PLI routine: $sps_create_transaction_stream:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_create_transaction_stream
#define __VCS_PLI_STUB_novas_call_phaseout_sps_create_transaction_stream
extern void novas_call_phaseout_sps_create_transaction_stream(int data, int reason);
#pragma weak novas_call_phaseout_sps_create_transaction_stream
void novas_call_phaseout_sps_create_transaction_stream(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_create_transaction_stream");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_create_transaction_stream");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_create_transaction_stream");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_create_transaction_stream)(int data, int reason) = novas_call_phaseout_sps_create_transaction_stream;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_create_transaction_stream */

/* PLI routine: $sps_begin_transaction:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_begin_transaction
#define __VCS_PLI_STUB_novas_call_phaseout_sps_begin_transaction
extern void novas_call_phaseout_sps_begin_transaction(int data, int reason);
#pragma weak novas_call_phaseout_sps_begin_transaction
void novas_call_phaseout_sps_begin_transaction(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_begin_transaction");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_begin_transaction");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_begin_transaction");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_begin_transaction)(int data, int reason) = novas_call_phaseout_sps_begin_transaction;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_begin_transaction */

/* PLI routine: $sps_end_transaction:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_end_transaction
#define __VCS_PLI_STUB_novas_call_phaseout_sps_end_transaction
extern void novas_call_phaseout_sps_end_transaction(int data, int reason);
#pragma weak novas_call_phaseout_sps_end_transaction
void novas_call_phaseout_sps_end_transaction(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_end_transaction");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_end_transaction");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_end_transaction");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_end_transaction)(int data, int reason) = novas_call_phaseout_sps_end_transaction;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_end_transaction */

/* PLI routine: $sps_free_transaction:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_free_transaction
#define __VCS_PLI_STUB_novas_call_phaseout_sps_free_transaction
extern void novas_call_phaseout_sps_free_transaction(int data, int reason);
#pragma weak novas_call_phaseout_sps_free_transaction
void novas_call_phaseout_sps_free_transaction(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_free_transaction");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_free_transaction");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_free_transaction");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_free_transaction)(int data, int reason) = novas_call_phaseout_sps_free_transaction;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_free_transaction */

/* PLI routine: $sps_add_attribute:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_add_attribute
#define __VCS_PLI_STUB_novas_call_phaseout_sps_add_attribute
extern void novas_call_phaseout_sps_add_attribute(int data, int reason);
#pragma weak novas_call_phaseout_sps_add_attribute
void novas_call_phaseout_sps_add_attribute(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_add_attribute");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_add_attribute");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_add_attribute");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_add_attribute)(int data, int reason) = novas_call_phaseout_sps_add_attribute;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_add_attribute */

/* PLI routine: $sps_update_label:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_update_label
#define __VCS_PLI_STUB_novas_call_phaseout_sps_update_label
extern void novas_call_phaseout_sps_update_label(int data, int reason);
#pragma weak novas_call_phaseout_sps_update_label
void novas_call_phaseout_sps_update_label(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_update_label");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_update_label");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_update_label");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_update_label)(int data, int reason) = novas_call_phaseout_sps_update_label;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_update_label */

/* PLI routine: $sps_add_relation:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_add_relation
#define __VCS_PLI_STUB_novas_call_phaseout_sps_add_relation
extern void novas_call_phaseout_sps_add_relation(int data, int reason);
#pragma weak novas_call_phaseout_sps_add_relation
void novas_call_phaseout_sps_add_relation(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_add_relation");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_add_relation");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_add_relation");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_add_relation)(int data, int reason) = novas_call_phaseout_sps_add_relation;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_add_relation */

/* PLI routine: $fsdbWhatif:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbWhatif
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbWhatif
extern void novas_call_phaseout_fsdbWhatif(int data, int reason);
#pragma weak novas_call_phaseout_fsdbWhatif
void novas_call_phaseout_fsdbWhatif(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbWhatif");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbWhatif");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbWhatif");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbWhatif)(int data, int reason) = novas_call_phaseout_fsdbWhatif;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbWhatif */

/* PLI routine: $paa_init:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_paa_init
#define __VCS_PLI_STUB_novas_call_phaseout_paa_init
extern void novas_call_phaseout_paa_init(int data, int reason);
#pragma weak novas_call_phaseout_paa_init
void novas_call_phaseout_paa_init(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_paa_init");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_paa_init");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_paa_init");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_paa_init)(int data, int reason) = novas_call_phaseout_paa_init;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_paa_init */

/* PLI routine: $paa_sync:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_paa_sync
#define __VCS_PLI_STUB_novas_call_phaseout_paa_sync
extern void novas_call_phaseout_paa_sync(int data, int reason);
#pragma weak novas_call_phaseout_paa_sync
void novas_call_phaseout_paa_sync(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_paa_sync");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_paa_sync");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_paa_sync");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_paa_sync)(int data, int reason) = novas_call_phaseout_paa_sync;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_paa_sync */

/* PLI routine: $fsdbDumpClassMethod:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassMethod
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassMethod
extern void novas_call_phaseout_fsdbDumpClassMethod(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpClassMethod
void novas_call_phaseout_fsdbDumpClassMethod(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpClassMethod");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpClassMethod");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpClassMethod");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpClassMethod)(int data, int reason) = novas_call_phaseout_fsdbDumpClassMethod;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassMethod */

/* PLI routine: $fsdbSuppressClassMethod:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassMethod
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassMethod
extern void novas_call_phaseout_fsdbSuppressClassMethod(int data, int reason);
#pragma weak novas_call_phaseout_fsdbSuppressClassMethod
void novas_call_phaseout_fsdbSuppressClassMethod(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbSuppressClassMethod");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbSuppressClassMethod");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbSuppressClassMethod");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbSuppressClassMethod)(int data, int reason) = novas_call_phaseout_fsdbSuppressClassMethod;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassMethod */

/* PLI routine: $fsdbSuppressClassProp:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassProp
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassProp
extern void novas_call_phaseout_fsdbSuppressClassProp(int data, int reason);
#pragma weak novas_call_phaseout_fsdbSuppressClassProp
void novas_call_phaseout_fsdbSuppressClassProp(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbSuppressClassProp");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbSuppressClassProp");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbSuppressClassProp");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbSuppressClassProp)(int data, int reason) = novas_call_phaseout_fsdbSuppressClassProp;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbSuppressClassProp */

/* PLI routine: $fsdbDumpMDAByFile:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpMDAByFile
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpMDAByFile
extern void novas_call_phaseout_fsdbDumpMDAByFile(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpMDAByFile
void novas_call_phaseout_fsdbDumpMDAByFile(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpMDAByFile");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpMDAByFile");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpMDAByFile");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpMDAByFile)(int data, int reason) = novas_call_phaseout_fsdbDumpMDAByFile;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpMDAByFile */

/* PLI routine: $fsdbTrans_create_stream_begin:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_begin
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_begin
extern void novas_call_phaseout_fsdbEvent_create_stream_begin(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_create_stream_begin
void novas_call_phaseout_fsdbEvent_create_stream_begin(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_create_stream_begin");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_create_stream_begin");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_create_stream_begin");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_create_stream_begin)(int data, int reason) = novas_call_phaseout_fsdbEvent_create_stream_begin;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_begin */

/* PLI routine: $fsdbTrans_define_attribute:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_stream_attribute
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_stream_attribute
extern void novas_call_phaseout_fsdbEvent_add_stream_attribute(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_add_stream_attribute
void novas_call_phaseout_fsdbEvent_add_stream_attribute(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_add_stream_attribute");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_add_stream_attribute");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_add_stream_attribute");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_add_stream_attribute)(int data, int reason) = novas_call_phaseout_fsdbEvent_add_stream_attribute;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_stream_attribute */

/* PLI routine: $fsdbTrans_create_stream_end:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_end
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_end
extern void novas_call_phaseout_fsdbEvent_create_stream_end(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_create_stream_end
void novas_call_phaseout_fsdbEvent_create_stream_end(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_create_stream_end");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_create_stream_end");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_create_stream_end");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_create_stream_end)(int data, int reason) = novas_call_phaseout_fsdbEvent_create_stream_end;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_create_stream_end */

/* PLI routine: $fsdbTrans_begin:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_begin
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_begin
extern void novas_call_phaseout_fsdbEvent_begin(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_begin
void novas_call_phaseout_fsdbEvent_begin(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_begin");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_begin");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_begin");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_begin)(int data, int reason) = novas_call_phaseout_fsdbEvent_begin;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_begin */

/* PLI routine: $fsdbTrans_set_label:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_set_label
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_set_label
extern void novas_call_phaseout_fsdbEvent_set_label(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_set_label
void novas_call_phaseout_fsdbEvent_set_label(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_set_label");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_set_label");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_set_label");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_set_label)(int data, int reason) = novas_call_phaseout_fsdbEvent_set_label;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_set_label */

/* PLI routine: $fsdbTrans_add_attribute:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute
extern void novas_call_phaseout_fsdbEvent_add_attribute(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_add_attribute
void novas_call_phaseout_fsdbEvent_add_attribute(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_add_attribute");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_add_attribute");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_add_attribute");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_add_attribute)(int data, int reason) = novas_call_phaseout_fsdbEvent_add_attribute;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute */

/* PLI routine: $fsdbTrans_add_tag:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_tag
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_tag
extern void novas_call_phaseout_fsdbEvent_add_tag(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_add_tag
void novas_call_phaseout_fsdbEvent_add_tag(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_add_tag");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_add_tag");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_add_tag");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_add_tag)(int data, int reason) = novas_call_phaseout_fsdbEvent_add_tag;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_tag */

/* PLI routine: $fsdbTrans_end:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_end
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_end
extern void novas_call_phaseout_fsdbEvent_end(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_end
void novas_call_phaseout_fsdbEvent_end(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_end");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_end");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_end");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_end)(int data, int reason) = novas_call_phaseout_fsdbEvent_end;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_end */

/* PLI routine: $fsdbTrans_add_relation:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_relation
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_relation
extern void novas_call_phaseout_fsdbEvent_add_relation(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_add_relation
void novas_call_phaseout_fsdbEvent_add_relation(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_add_relation");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_add_relation");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_add_relation");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_add_relation)(int data, int reason) = novas_call_phaseout_fsdbEvent_add_relation;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_relation */

/* PLI routine: $fsdbTrans_get_error_code:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_get_error_code
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_get_error_code
extern void novas_call_phaseout_fsdbEvent_get_error_code(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_get_error_code
void novas_call_phaseout_fsdbEvent_get_error_code(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_get_error_code");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_get_error_code");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_get_error_code");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_get_error_code)(int data, int reason) = novas_call_phaseout_fsdbEvent_get_error_code;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_get_error_code */

/* PLI routine: $fsdbTrans_add_stream_attribute:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_stream_attribute
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_stream_attribute
extern void novas_call_phaseout_fsdbTrans_add_stream_attribute(int data, int reason);
#pragma weak novas_call_phaseout_fsdbTrans_add_stream_attribute
void novas_call_phaseout_fsdbTrans_add_stream_attribute(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbTrans_add_stream_attribute");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbTrans_add_stream_attribute");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbTrans_add_stream_attribute");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbTrans_add_stream_attribute)(int data, int reason) = novas_call_phaseout_fsdbTrans_add_stream_attribute;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_stream_attribute */

/* PLI routine: $fsdbTrans_add_scope_attribute:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_scope_attribute
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_scope_attribute
extern void novas_call_phaseout_fsdbTrans_add_scope_attribute(int data, int reason);
#pragma weak novas_call_phaseout_fsdbTrans_add_scope_attribute
void novas_call_phaseout_fsdbTrans_add_scope_attribute(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbTrans_add_scope_attribute");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbTrans_add_scope_attribute");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbTrans_add_scope_attribute");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbTrans_add_scope_attribute)(int data, int reason) = novas_call_phaseout_fsdbTrans_add_scope_attribute;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbTrans_add_scope_attribute */

/* PLI routine: $sps_interactive:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_interactive
#define __VCS_PLI_STUB_novas_call_phaseout_sps_interactive
extern void novas_call_phaseout_sps_interactive(int data, int reason);
#pragma weak novas_call_phaseout_sps_interactive
void novas_call_phaseout_sps_interactive(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_interactive");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_interactive");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_interactive");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_interactive)(int data, int reason) = novas_call_phaseout_sps_interactive;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_interactive */

/* PLI routine: $sps_test:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_test
#define __VCS_PLI_STUB_novas_call_phaseout_sps_test
extern void novas_call_phaseout_sps_test(int data, int reason);
#pragma weak novas_call_phaseout_sps_test
void novas_call_phaseout_sps_test(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_test");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_test");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_test");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_test)(int data, int reason) = novas_call_phaseout_sps_test;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_test */

/* PLI routine: $fsdbDumpClassObject:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObject
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObject
extern void novas_call_phaseout_fsdbDumpClassObject(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpClassObject
void novas_call_phaseout_fsdbDumpClassObject(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpClassObject");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpClassObject");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpClassObject");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpClassObject)(int data, int reason) = novas_call_phaseout_fsdbDumpClassObject;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObject */

/* PLI routine: $fsdbDumpClassObjectByFile:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObjectByFile
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObjectByFile
extern void novas_call_phaseout_fsdbDumpClassObjectByFile(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpClassObjectByFile
void novas_call_phaseout_fsdbDumpClassObjectByFile(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpClassObjectByFile");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpClassObjectByFile");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpClassObjectByFile");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpClassObjectByFile)(int data, int reason) = novas_call_phaseout_fsdbDumpClassObjectByFile;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpClassObjectByFile */

/* PLI routine: $fsdbTrans_add_attribute_expand:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute_expand
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute_expand
extern void novas_call_phaseout_fsdbEvent_add_attribute_expand(int data, int reason);
#pragma weak novas_call_phaseout_fsdbEvent_add_attribute_expand
void novas_call_phaseout_fsdbEvent_add_attribute_expand(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbEvent_add_attribute_expand");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbEvent_add_attribute_expand");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbEvent_add_attribute_expand");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbEvent_add_attribute_expand)(int data, int reason) = novas_call_phaseout_fsdbEvent_add_attribute_expand;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbEvent_add_attribute_expand */

/* PLI routine: $ridbDump:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_ridbDump
#define __VCS_PLI_STUB_novas_call_phaseout_ridbDump
extern void novas_call_phaseout_ridbDump(int data, int reason);
#pragma weak novas_call_phaseout_ridbDump
void novas_call_phaseout_ridbDump(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_ridbDump");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_ridbDump");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_ridbDump");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_ridbDump)(int data, int reason) = novas_call_phaseout_ridbDump;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_ridbDump */

/* PLI routine: $sps_flush_file:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_sps_flush_file
#define __VCS_PLI_STUB_novas_call_phaseout_sps_flush_file
extern void novas_call_phaseout_sps_flush_file(int data, int reason);
#pragma weak novas_call_phaseout_sps_flush_file
void novas_call_phaseout_sps_flush_file(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_sps_flush_file");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_sps_flush_file");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_sps_flush_file");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_sps_flush_file)(int data, int reason) = novas_call_phaseout_sps_flush_file;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_sps_flush_file */

/* PLI routine: $fsdbDumpSingle:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpSingle
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpSingle
extern void novas_call_phaseout_fsdbDumpSingle(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpSingle
void novas_call_phaseout_fsdbDumpSingle(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpSingle");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpSingle");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpSingle");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpSingle)(int data, int reason) = novas_call_phaseout_fsdbDumpSingle;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpSingle */

/* PLI routine: $fsdbDumpIO:call */
#ifndef __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpIO
#define __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpIO
extern void novas_call_phaseout_fsdbDumpIO(int data, int reason);
#pragma weak novas_call_phaseout_fsdbDumpIO
void novas_call_phaseout_fsdbDumpIO(int data, int reason)
{
    static int _vcs_pli_stub_initialized_ = 0;
    static void (*_vcs_pli_fp_)(int data, int reason) = NULL;
    if (!_vcs_pli_stub_initialized_) {
        _vcs_pli_stub_initialized_ = 1;
        _vcs_pli_fp_ = (void (*)(int data, int reason)) dlsym(RTLD_NEXT, "novas_call_phaseout_fsdbDumpIO");
        if (_vcs_pli_fp_ == NULL) {
            _vcs_pli_fp_ = (void (*)(int data, int reason)) VCS_dlsymLookup("novas_call_phaseout_fsdbDumpIO");
        }
    }
    if (_vcs_pli_fp_) {
        _vcs_pli_fp_(data, reason);
    } else {
        vcsMsgReportNoSource1("PLI-DIFNF", "novas_call_phaseout_fsdbDumpIO");
    }
}
void (*__vcs_pli_dummy_reference_novas_call_phaseout_fsdbDumpIO)(int data, int reason) = novas_call_phaseout_fsdbDumpIO;
#endif /* __VCS_PLI_STUB_novas_call_phaseout_fsdbDumpIO */

#ifdef __cplusplus
}
#endif
