import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10084 = true := by
  decide +kernel

theorem tot10084 : totK PD2M8K2 D2M8K2.t10084 = [0, 0, 172390137915, 480083837375, 223082313635, 12084068872, 0, 0] := by
  decide +kernel

theorem rows10085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10085 = true := by
  decide +kernel

theorem tot10085 : totK PD2M8K2 D2M8K2.t10085 = [0, 0, 0, 367858214993, 460725321854, 43860592649, 0, 0] := by
  decide +kernel

theorem rows10086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10086 = true := by
  decide +kernel

theorem tot10086 : totK PD2M8K2 D2M8K2.t10086 = [0, 0, 156763095093, 385332302090, 277441648541, 65477632870, 1330264907, 0] := by
  decide +kernel

theorem rows10087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10087 = true := by
  decide +kernel

theorem tot10087 : totK PD2M8K2 D2M8K2.t10087 = [0, 0, 156416194345, 445955581094, 278718346940, 19359168443, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
