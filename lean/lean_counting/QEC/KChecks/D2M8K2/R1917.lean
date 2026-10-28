import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7668 = true := by
  decide +kernel

theorem tot7668 : totK PD2M8K2 D2M8K2.t7668 = [0, 0, 0, 257263794743, 470890372074, 155950283336, 10122467735, 0] := by
  decide +kernel

theorem rows7669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7669 = true := by
  decide +kernel

theorem tot7669 : totK PD2M8K2 D2M8K2.t7669 = [0, 0, 0, 173444053491, 481837596483, 193563421800, 9427200455, 0] := by
  decide +kernel

theorem rows7670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7670 = true := by
  decide +kernel

theorem tot7670 : totK PD2M8K2 D2M8K2.t7670 = [0, 0, 0, 159089179506, 457585776687, 225979249811, 17195321440, 0] := by
  decide +kernel

theorem rows7671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7671 = true := by
  decide +kernel

theorem tot7671 : totK PD2M8K2 D2M8K2.t7671 = [0, 0, 0, 0, 307913455033, 431648349399, 80490683177, 1275377855] := by
  decide +kernel

end QECKChecks.D2M8K2
