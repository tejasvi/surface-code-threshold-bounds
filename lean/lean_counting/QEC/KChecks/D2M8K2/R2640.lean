import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10560 = true := by
  decide +kernel

theorem tot10560 : totK PD2M8K2 D2M8K2.t10560 = [0, 0, 159389664742, 430199335944, 264153474248, 53066829317, 1186940923, 0] := by
  decide +kernel

theorem rows10561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10561 = true := by
  decide +kernel

theorem tot10561 : totK PD2M8K2 D2M8K2.t10561 = [0, 0, 170076761552, 433418719217, 263688388982, 20752648125, 0, 0] := by
  decide +kernel

theorem rows10562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10562 = true := by
  decide +kernel

theorem tot10562 : totK PD2M8K2 D2M8K2.t10562 = [0, 0, 91681601894, 414837026691, 354988078480, 33755669652, 0, 0] := by
  decide +kernel

theorem rows10563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10563 = true := by
  decide +kernel

theorem tot10563 : totK PD2M8K2 D2M8K2.t10563 = [0, 0, 0, 279401293481, 518026185390, 103431677934, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
