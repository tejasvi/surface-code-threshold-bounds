import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13848 = true := by
  decide +kernel

theorem tot13848 : totK PD2M8K2 D2M8K2.t13848 = [0, 106076479534, 401407699304, 309966888738, 47832826852, 1021600638, 0, 0] := by
  decide +kernel

theorem rows13849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13849 = true := by
  decide +kernel

theorem tot13849 : totK PD2M8K2 D2M8K2.t13849 = [0, 7529949136, 287620112800, 452140959285, 101456334442, 3552795014, 0, 0] := by
  decide +kernel

theorem rows13850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13850 = true := by
  decide +kernel

theorem tot13850 : totK PD2M8K2 D2M8K2.t13850 = [0, 192225415197, 459813958456, 235449122323, 20829303670, 0, 0, 0] := by
  decide +kernel

theorem rows13851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13851 = true := by
  decide +kernel

theorem tot13851 : totK PD2M8K2 D2M8K2.t13851 = [0, 206376413416, 486371910723, 211746661495, 9870528108, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
