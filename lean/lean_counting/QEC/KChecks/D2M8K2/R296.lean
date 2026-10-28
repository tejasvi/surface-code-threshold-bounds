import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1184 = true := by
  decide +kernel

theorem tot1184 : totK PD2M8K2 D2M8K2.t1184 = [94975436091, 412691546929, 354751395482, 37855386459, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1185 = true := by
  decide +kernel

theorem tot1185 : totK PD2M8K2 D2M8K2.t1185 = [0, 213491336576, 479217840365, 179779348917, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows1186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1186 = true := by
  decide +kernel

theorem tot1186 : totK PD2M8K2 D2M8K2.t1186 = [105087762688, 352390012099, 339609887844, 88338164864, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows1187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1187 = true := by
  decide +kernel

theorem tot1187 : totK PD2M8K2 D2M8K2.t1187 = [183334120149, 437987964764, 253348936224, 26880152344, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
