import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14480 = true := by
  decide +kernel

theorem tot14480 : totK PD2M8K2 D2M8K2.t14480 = [0, 0, 211805871657, 490869048522, 182641650143, 5206224793, 0, 0] := by
  decide +kernel

theorem rows14481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14481 = true := by
  decide +kernel

theorem tot14481 : totK PD2M8K2 D2M8K2.t14481 = [0, 155116473731, 341356916503, 308141268634, 113062553280, 6524090962, 0, 0] := by
  decide +kernel

theorem rows14482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14482 = true := by
  decide +kernel

theorem tot14482 : totK PD2M8K2 D2M8K2.t14482 = [0, 175713225586, 485483115268, 235133235841, 12236445388, 0, 0, 0] := by
  decide +kernel

theorem rows14483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14483 = true := by
  decide +kernel

theorem tot14483 : totK PD2M8K2 D2M8K2.t14483 = [0, 0, 268961766877, 495203734230, 134905162623, 4009909289, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
