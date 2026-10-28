import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14068 = true := by
  decide +kernel

theorem tot14068 : totK PD2M8K2 D2M8K2.t14068 = [0, 179799707541, 465859228347, 255330101980, 23046987921, 0, 0, 0] := by
  decide +kernel

theorem rows14069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14069 = true := by
  decide +kernel

theorem tot14069 : totK PD2M8K2 D2M8K2.t14069 = [0, 155451780030, 451708080033, 265404973445, 21716347659, 0, 0, 0] := by
  decide +kernel

theorem rows14070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14070 = true := by
  decide +kernel

theorem tot14070 : totK PD2M8K2 D2M8K2.t14070 = [0, 0, 231004215618, 488616354903, 160742804686, 7233348802, 0, 0] := by
  decide +kernel

theorem rows14071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14071 = true := by
  decide +kernel

theorem tot14071 : totK PD2M8K2 D2M8K2.t14071 = [0, 70914634579, 280731173063, 385375878776, 130957669036, 6017336459, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
