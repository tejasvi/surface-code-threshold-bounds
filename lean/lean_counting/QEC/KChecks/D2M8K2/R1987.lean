import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7948 = true := by
  decide +kernel

theorem tot7948 : totK PD2M8K2 D2M8K2.t7948 = [0, 0, 190476769263, 468914046694, 222804835533, 12373752831, 0, 0] := by
  decide +kernel

theorem rows7949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7949 = true := by
  decide +kernel

theorem tot7949 : totK PD2M8K2 D2M8K2.t7949 = [0, 0, 47475205104, 326612975437, 424307688745, 83375649384, 1164319620, 0] := by
  decide +kernel

theorem rows7950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7950 = true := by
  decide +kernel

theorem tot7950 : totK PD2M8K2 D2M8K2.t7950 = [0, 0, 0, 199122152211, 471435356955, 177248500397, 11819130176, 0] := by
  decide +kernel

theorem rows7951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7951 = true := by
  decide +kernel

theorem tot7951 : totK PD2M8K2 D2M8K2.t7951 = [0, 0, 219637430294, 464536366563, 206505161285, 12081578678, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
