import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15308 = true := by
  decide +kernel

theorem tot15308 : totK PD2M8K2 D2M8K2.t15308 = [0, 0, 0, 324908633063, 485946475150, 75719879586, 1096505104, 0] := by
  decide +kernel

theorem rows15309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15309 = true := by
  decide +kernel

theorem tot15309 : totK PD2M8K2 D2M8K2.t15309 = [0, 0, 112582420456, 417578503022, 345993952468, 29625298637, 0, 0] := by
  decide +kernel

theorem rows15310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15310 = true := by
  decide +kernel

theorem tot15310 : totK PD2M8K2 D2M8K2.t15310 = [0, 0, 183901941007, 454763986473, 232342489987, 13419393785, 0, 0] := by
  decide +kernel

theorem rows15311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15311 = true := by
  decide +kernel

theorem tot15311 : totK PD2M8K2 D2M8K2.t15311 = [0, 0, 123652271936, 426077196383, 312258934700, 28567347540, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
