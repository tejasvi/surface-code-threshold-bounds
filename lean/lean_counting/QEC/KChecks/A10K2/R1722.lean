import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6888 = true := by
  decide +kernel

theorem tot6888 : totK PA10K2 A10K2.t6888 = [0, 440619718765, 1460566208189, 1590536026996, 970602795372, 406326978808, 43709387373, 0, 0, 0] := by
  decide +kernel

theorem rows6889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6889 = true := by
  decide +kernel

theorem tot6889 : totK PA10K2 A10K2.t6889 = [0, 318934636219, 1521338018639, 2160411331054, 841659878434, 62506613362, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6890 = true := by
  decide +kernel

theorem tot6890 : totK PA10K2 A10K2.t6890 = [0, 0, 548551054052, 1833328429711, 1832562370961, 490386927909, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows6891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6891 = true := by
  decide +kernel

theorem tot6891 : totK PA10K2 A10K2.t6891 = [0, 559395152186, 1849499157201, 1817185587281, 599609809152, 49914836386, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
