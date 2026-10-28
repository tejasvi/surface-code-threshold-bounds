import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6248 = true := by
  decide +kernel

theorem tot6248 : totK PD2M8K2 D2M8K2.t6248 = [167558872695, 442473459728, 279132241869, 30211536632, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6249 = true := by
  decide +kernel

theorem tot6249 : totK PD2M8K2 D2M8K2.t6249 = [164842185560, 475530965033, 250860827990, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6250 = true := by
  decide +kernel

theorem tot6250 : totK PD2M8K2 D2M8K2.t6250 = [0, 277377770316, 520427519851, 106160763617, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6251 = true := by
  decide +kernel

theorem tot6251 : totK PD2M8K2 D2M8K2.t6251 = [0, 208892720871, 493941128189, 176954037441, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
