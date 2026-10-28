import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13264 = true := by
  decide +kernel

theorem tot13264 : totK PD2M8K2 D2M8K2.t13264 = [0, 155484015133, 351411207526, 313191655573, 98113004402, 3880716147, 0, 0] := by
  decide +kernel

theorem rows13265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13265 = true := by
  decide +kernel

theorem tot13265 : totK PD2M8K2 D2M8K2.t13265 = [0, 174544416507, 479569592448, 237221041056, 14345094952, 0, 0, 0] := by
  decide +kernel

theorem rows13266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13266 = true := by
  decide +kernel

theorem tot13266 : totK PD2M8K2 D2M8K2.t13266 = [0, 0, 273890762846, 498112658494, 125030032669, 2651406374, 0, 0] := by
  decide +kernel

theorem rows13267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13267 = true := by
  decide +kernel

theorem tot13267 : totK PD2M8K2 D2M8K2.t13267 = [0, 0, 185386877585, 475381683283, 221044769330, 20759876372, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
