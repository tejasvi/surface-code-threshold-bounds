import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t948 = true := by
  decide +kernel

theorem tot948 : totK PD2M8K2 D2M8K2.t948 = [0, 68961823636, 380989620868, 406615839525, 50163419175, 0, 0, 0] := by
  decide +kernel

theorem rows949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t949 = true := by
  decide +kernel

theorem tot949 : totK PD2M8K2 D2M8K2.t949 = [0, 17505498795, 216798789838, 481047175418, 159225806040, 5159868635, 0, 0] := by
  decide +kernel

theorem rows950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t950 = true := by
  decide +kernel

theorem tot950 : totK PD2M8K2 D2M8K2.t950 = [0, 193451316027, 461066746729, 237744935796, 23032851771, 0, 0, 0] := by
  decide +kernel

theorem rows951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t951 = true := by
  decide +kernel

theorem tot951 : totK PD2M8K2 D2M8K2.t951 = [0, 190768036276, 467277176285, 224059606151, 12423391470, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
