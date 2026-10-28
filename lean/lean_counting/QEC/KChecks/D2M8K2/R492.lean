import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1968 = true := by
  decide +kernel

theorem tot1968 : totK PD2M8K2 D2M8K2.t1968 = [0, 0, 172797753144, 461372517865, 236459758569, 12854385128, 0, 0] := by
  decide +kernel

theorem rows1969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1969 = true := by
  decide +kernel

theorem tot1969 : totK PD2M8K2 D2M8K2.t1969 = [0, 0, 220581501139, 492185505356, 166659873701, 4990270569, 0, 0] := by
  decide +kernel

theorem rows1970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1970 = true := by
  decide +kernel

theorem tot1970 : totK PD2M8K2 D2M8K2.t1970 = [0, 0, 188324239729, 453582501118, 216067283524, 16861767938, 0, 0] := by
  decide +kernel

theorem rows1971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1971 = true := by
  decide +kernel

theorem tot1971 : totK PD2M8K2 D2M8K2.t1971 = [0, 0, 155662754018, 486899524244, 242247841721, 6579586603, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
