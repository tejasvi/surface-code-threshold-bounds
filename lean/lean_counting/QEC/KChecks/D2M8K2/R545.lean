import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2180 = true := by
  decide +kernel

theorem tot2180 : totK PD2M8K2 D2M8K2.t2180 = [0, 0, 287708163108, 507774095254, 99464595066, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2181 = true := by
  decide +kernel

theorem tot2181 : totK PD2M8K2 D2M8K2.t2181 = [0, 82236245000, 326496067024, 370743043214, 104958091443, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2182 = true := by
  decide +kernel

theorem tot2182 : totK PD2M8K2 D2M8K2.t2182 = [0, 201468910355, 477205426021, 226069220590, 12662116064, 0, 0, 0] := by
  decide +kernel

theorem rows2183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2183 = true := by
  decide +kernel

theorem tot2183 : totK PD2M8K2 D2M8K2.t2183 = [0, 45418960504, 324861039879, 427609743983, 99158817243, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
