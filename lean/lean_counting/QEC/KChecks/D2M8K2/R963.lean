import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3852 = true := by
  decide +kernel

theorem tot3852 : totK PD2M8K2 D2M8K2.t3852 = [0, 106883738774, 380593804825, 380390264311, 46155902763, 0, 0, 0] := by
  decide +kernel

theorem rows3853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3853 = true := by
  decide +kernel

theorem tot3853 : totK PD2M8K2 D2M8K2.t3853 = [0, 181555755166, 469770356734, 240789363405, 13279294935, 0, 0, 0] := by
  decide +kernel

theorem rows3854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3854 = true := by
  decide +kernel

theorem tot3854 : totK PD2M8K2 D2M8K2.t3854 = [0, 204395254565, 479973890206, 213343066099, 14877743084, 0, 0, 0] := by
  decide +kernel

theorem rows3855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3855 = true := by
  decide +kernel

theorem tot3855 : totK PD2M8K2 D2M8K2.t3855 = [0, 187222919714, 459797545502, 244197838432, 20823395285, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
