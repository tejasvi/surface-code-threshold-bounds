import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5208 = true := by
  decide +kernel

theorem tot5208 : totK PD2M8K2 D2M8K2.t5208 = [0, 91519432074, 216483818532, 74985626900, 140145938467, 283241831618, 88149113051, 1493059870] := by
  decide +kernel

theorem rows5209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5209 = true := by
  decide +kernel

theorem tot5209 : totK PD2M8K2 D2M8K2.t5209 = [0, 174721501883, 454791880078, 240317823362, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows5210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5210 = true := by
  decide +kernel

theorem tot5210 : totK PD2M8K2 D2M8K2.t5210 = [0, 152146670825, 448185883702, 275798150850, 23678717390, 0, 0, 0] := by
  decide +kernel

theorem rows5211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5211 = true := by
  decide +kernel

theorem tot5211 : totK PD2M8K2 D2M8K2.t5211 = [0, 0, 272185629752, 506129590306, 110963415053, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
