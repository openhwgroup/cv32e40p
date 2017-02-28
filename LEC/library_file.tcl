
usage -auto

vpxmode
vpx set naming rule "%s_reg" -register -golden
vpx set naming rule "%L.%s" "%L[%d].%s" "%s" -instance
vpx set naming rule "%L.%s" "%L[%d].%s" "%s" -variable
vpx set undefined cell black_box -noascend -both
vpx set undriven signal Z -golden

tclmode
global IPS_PATH "../../"


vpxmode
add search path -library  /home/techlibs/tsmc/cln55lp/sc9_base_lvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_base_rvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_base_hvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_pmk_rvt_hvt/r0p0/lib 



read library -statetable -liberty -pg_pin -both                     \
               sc9_cln55lp_base_lvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_base_rvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_base_hvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_pmk_rvt_hvt_ss_typical_max_1p08v_125c.lib


tclmode
