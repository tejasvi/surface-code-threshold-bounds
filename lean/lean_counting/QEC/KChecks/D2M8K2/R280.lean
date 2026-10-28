import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1120 = true := by
  decide +kernel

theorem tot1120 : totK PD2M8K2 D2M8K2.t1120 = [0, 181054620258, 447810402232, 243111568587, 21891416118, 0, 0, 0] := by
  decide +kernel

theorem rows1121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1121 = true := by
  decide +kernel

theorem tot1121 : totK PD2M8K2 D2M8K2.t1121 = [0, 65981665209, 345626567887, 390498113628, 77362810748, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1122 = true := by
  decide +kernel

theorem tot1122 : totK PD2M8K2 D2M8K2.t1122 = [0, 0, 268128253276, 511607843078, 115728494677, 2158098333, 0, 0] := by
  decide +kernel

theorem rows1123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1123 = true := by
  decide +kernel

theorem tot1123 : totK PD2M8K2 D2M8K2.t1123 = [0, 206661003387, 456490421348, 218800590477, 26239244253, 1725911522, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
