import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5944 = true := by
  decide +kernel

theorem tot5944 : totK PD2M8K2 D2M8K2.t5944 = [0, 89165724567, 363762256616, 370414921257, 64514744710, 1075657031, 0, 0] := by
  decide +kernel

theorem rows5945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5945 = true := by
  decide +kernel

theorem tot5945 : totK PD2M8K2 D2M8K2.t5945 = [0, 0, 292574890938, 472787677685, 108001514156, 3804183361, 0, 0] := by
  decide +kernel

theorem rows5946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5946 = true := by
  decide +kernel

theorem tot5946 : totK PD2M8K2 D2M8K2.t5946 = [0, 173164107325, 436296459248, 273568651161, 30823611990, 0, 0, 0] := by
  decide +kernel

theorem rows5947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5947 = true := by
  decide +kernel

theorem tot5947 : totK PD2M8K2 D2M8K2.t5947 = [0, 211357373178, 480106804169, 202112664101, 11004568768, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
