import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16264 = true := by
  decide +kernel

theorem tot16264 : totK PD2M8K2 D2M8K2.t16264 = [0, 0, 0, 232186564898, 488386842024, 128876556533, 2330587781, 0] := by
  decide +kernel

theorem rows16265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16265 = true := by
  decide +kernel

theorem tot16265 : totK PD2M8K2 D2M8K2.t16265 = [0, 0, 0, 207354947386, 484373620834, 193785485750, 8337419369, 0] := by
  decide +kernel

theorem rows16266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16266 = true := by
  decide +kernel

theorem tot16266 : totK PD2M8K2 D2M8K2.t16266 = [0, 0, 0, 200042738501, 474665932104, 197315722848, 7756870157, 0] := by
  decide +kernel

theorem rows16267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16267 = true := by
  decide +kernel

theorem tot16267 : totK PD2M8K2 D2M8K2.t16267 = [0, 0, 134721454216, 320033690902, 317075716760, 145214900927, 13468148062, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
