import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9184 = true := by
  decide +kernel

theorem tot9184 : totK PD2M8K2 D2M8K2.t9184 = [174831780044, 435180168583, 273671885419, 30214580655, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9185 = true := by
  decide +kernel

theorem tot9185 : totK PD2M8K2 D2M8K2.t9185 = [173143656395, 484262781619, 246700322595, 12148017968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9186 = true := by
  decide +kernel

theorem tot9186 : totK PD2M8K2 D2M8K2.t9186 = [0, 238114564910, 451255108284, 198751802381, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows9187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9187 = true := by
  decide +kernel

theorem tot9187 : totK PD2M8K2 D2M8K2.t9187 = [0, 175765777659, 490656960289, 222457390396, 7994456143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
