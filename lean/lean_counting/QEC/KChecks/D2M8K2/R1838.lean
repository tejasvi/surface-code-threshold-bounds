import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7352 = true := by
  decide +kernel

theorem tot7352 : totK PD2M8K2 D2M8K2.t7352 = [0, 102765315917, 314589978131, 331727423420, 148771138452, 8209931632, 0, 0] := by
  decide +kernel

theorem rows7353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7353 = true := by
  decide +kernel

theorem tot7353 : totK PD2M8K2 D2M8K2.t7353 = [0, 163347312541, 449817678358, 282137272312, 30310421197, 0, 0, 0] := by
  decide +kernel

theorem rows7354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7354 = true := by
  decide +kernel

theorem tot7354 : totK PD2M8K2 D2M8K2.t7354 = [0, 175351648363, 467269864840, 248164694619, 17227132151, 0, 0, 0] := by
  decide +kernel

theorem rows7355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7355 = true := by
  decide +kernel

theorem tot7355 : totK PD2M8K2 D2M8K2.t7355 = [0, 0, 245093889137, 516739587613, 138934750018, 2309606161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
