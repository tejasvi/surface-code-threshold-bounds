import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7376 = true := by
  decide +kernel

theorem tot7376 : totK PD2M8K2 D2M8K2.t7376 = [0, 0, 45508623606, 307262427915, 406588621330, 93415088064, 3552795014, 0] := by
  decide +kernel

theorem rows7377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7377 = true := by
  decide +kernel

theorem tot7377 : totK PD2M8K2 D2M8K2.t7377 = [0, 0, 187742790454, 462470565853, 241463367611, 20829303670, 0, 0] := by
  decide +kernel

theorem rows7378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7378 = true := by
  decide +kernel

theorem tot7378 : totK PD2M8K2 D2M8K2.t7378 = [0, 0, 179084493957, 480412592579, 232929084448, 9822458397, 0, 0] := by
  decide +kernel

theorem rows7379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7379 = true := by
  decide +kernel

theorem tot7379 : totK PD2M8K2 D2M8K2.t7379 = [0, 166746023996, 381062290307, 262825146117, 103627135012, 12072404235, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
