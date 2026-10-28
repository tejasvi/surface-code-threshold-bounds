import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14236 = true := by
  decide +kernel

theorem tot14236 : totK PD2M8K2 D2M8K2.t14236 = [139334739811, 369441299359, 280784955215, 108191785095, 6778541047, 0, 0, 0] := by
  decide +kernel

theorem rows14237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14237 = true := by
  decide +kernel

theorem tot14237 : totK PD2M8K2 D2M8K2.t14237 = [168610438442, 439587881777, 277274404602, 30105385767, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14238 = true := by
  decide +kernel

theorem tot14238 : totK PD2M8K2 D2M8K2.t14238 = [112767649574, 428954312871, 322622955442, 27951092861, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14239 = true := by
  decide +kernel

theorem tot14239 : totK PD2M8K2 D2M8K2.t14239 = [0, 214058384550, 482866094354, 181515603963, 9587713104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
