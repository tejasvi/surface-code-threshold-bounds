import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15144 = true := by
  decide +kernel

theorem tot15144 : totK PD2M8K2 D2M8K2.t15144 = [0, 150494801662, 438438260039, 294709438252, 36004800687, 0, 0, 0] := by
  decide +kernel

theorem rows15145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15145 = true := by
  decide +kernel

theorem tot15145 : totK PD2M8K2 D2M8K2.t15145 = [0, 206035448186, 442459204773, 217168337121, 18260330531, 0, 0, 0] := by
  decide +kernel

theorem rows15146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15146 = true := by
  decide +kernel

theorem tot15146 : totK PD2M8K2 D2M8K2.t15146 = [0, 22303069631, 329421932540, 450645651508, 78503310371, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15147 = true := by
  decide +kernel

theorem tot15147 : totK PD2M8K2 D2M8K2.t15147 = [0, 85552730166, 307119971011, 388803275149, 102902423336, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
