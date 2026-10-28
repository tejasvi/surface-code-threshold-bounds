import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7000 = true := by
  decide +kernel

theorem tot7000 : totK PD2M8K2 D2M8K2.t7000 = [0, 0, 185889172130, 475008750859, 207108348123, 14703944056, 0, 0] := by
  decide +kernel

theorem rows7001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7001 = true := by
  decide +kernel

theorem tot7001 : totK PD2M8K2 D2M8K2.t7001 = [0, 0, 185054592900, 477357519302, 194676853814, 6335770431, 0, 0] := by
  decide +kernel

theorem rows7002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7002 = true := by
  decide +kernel

theorem tot7002 : totK PD2M8K2 D2M8K2.t7002 = [0, 0, 53817288941, 350309605864, 380460850596, 60264244436, 1200365979, 0] := by
  decide +kernel

theorem rows7003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7003 = true := by
  decide +kernel

theorem tot7003 : totK PD2M8K2 D2M8K2.t7003 = [0, 0, 91512766031, 413008689484, 360570738921, 30279270475, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
