
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
add search path -library  /home/techlibs/tsmc/cln55lp/sc9_base_lvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_base_rvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_base_hvt/r0p0/lib /home/techlibs/tsmc/cln55lp/sc9_pmk_rvt_hvt/r0p0/lib  /home/techlibs/tsmc/cln55lp/IPS/SESAME-CLICK_TSMC_55nm_LP_HVT_v4.0.0_FINAL_DELIVERY-2/SESAME-CLICK_FrontEnd/SESAME-CLICK_LIB/NLM  /home/igor/Desktop/prj/PULP/GAP/fe/ips/fll/LIB /home/techlibs/tsmc/cln55lp/IPS/DOLPHIN_SRAM/SpRAM_2kx32m8s2/FrontEnd/LIBERTY_v1  /home/techlibs/tsmc/cln55lp/IPS/DOLPHIN_SRAM/SpRAM_4kx64m8s2/FrontEnd/LIBERTY_v1  /home/techlibs/tsmc/cln55lp/IPS/DOLPHIN_SRAM/SpRAM_1kx32m8s2/FrontEnd/LIBERTY_v1  /home/techlibs/tsmc/cln55lp/IPS/EFUSE/efuse/Front_End/timing_power_noise/NLDM/tef55lp128x8hd_ph_140a /home/techlibs/tsmc/cln55lp/IPS/TSMC_55_MEM_CUTS/ts3n55lplla1024x64m8_200a/NLDM



read library -statetable -liberty -pg_pin -both                     \
               sc9_cln55lp_base_lvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_base_rvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_base_hvt_ss_typical_max_1p08v_125c.lib   \
               sc9_cln55lp_pmk_rvt_hvt_ss_typical_max_1p08v_125c.lib  \
               TCDM_2048_32_BE_WC_SS_1V08_125c.lib                   \
               L2_4096_64_BE_ERS_WC_SS_1V08_125c.lib                 \
               tsmc55lp_FLL_ss_typical_max_1p08v_125c.lib            \
               tef55lp128x8hd_ph_140a_wc.lib                         \
               ts3n55lplla1024x64m8_200a_ss1p08v125c.lib             \
               SESAME-CLICK_TSMC_55nm_LP_HVT_SS_1V08_125C_nlm.lib    \
               TCDM_1024_32_BE_WC_SS_1V08_125c.lib


tclmode
