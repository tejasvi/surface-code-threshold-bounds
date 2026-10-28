import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13732 = true := by
  decide +kernel

theorem tot13732 : totK PD2M8K2 D2M8K2.t13732 = [0, 0, 196922479418, 466285122652, 194475874273, 11991925116, 0, 0] := by
  decide +kernel

theorem rows13733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13733 = true := by
  decide +kernel

theorem tot13733 : totK PD2M8K2 D2M8K2.t13733 = [0, 167188989745, 434612559591, 278684820222, 31126903542, 0, 0, 0] := by
  decide +kernel

theorem rows13734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13734 = true := by
  decide +kernel

theorem tot13734 : totK PD2M8K2 D2M8K2.t13734 = [0, 195713854393, 450376924825, 218409793444, 17028259732, 0, 0, 0] := by
  decide +kernel

theorem rows13735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13735 = true := by
  decide +kernel

theorem tot13735 : totK PD2M8K2 D2M8K2.t13735 = [0, 11526037961, 318333873721, 464550693129, 80665760373, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
