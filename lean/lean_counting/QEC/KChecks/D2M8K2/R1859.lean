import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7436 = true := by
  decide +kernel

theorem tot7436 : totK PD2M8K2 D2M8K2.t7436 = [0, 0, 178620755131, 450989734897, 249846535859, 22828318141, 0, 0] := by
  decide +kernel

theorem rows7437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7437 = true := by
  decide +kernel

theorem tot7437 : totK PD2M8K2 D2M8K2.t7437 = [0, 0, 105517819276, 429088819711, 304411938683, 27473615024, 0, 0] := by
  decide +kernel

theorem rows7438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7438 = true := by
  decide +kernel

theorem tot7438 : totK PD2M8K2 D2M8K2.t7438 = [0, 0, 0, 305629539583, 468694781068, 90168121006, 1095107716, 0] := by
  decide +kernel

theorem rows7439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7439 = true := by
  decide +kernel

theorem tot7439 : totK PD2M8K2 D2M8K2.t7439 = [0, 169606407816, 349315023727, 140451211973, 145532093446, 79881184057, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
