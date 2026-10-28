import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6532 = true := by
  decide +kernel

theorem tot6532 : totK PD2M8K2 D2M8K2.t6532 = [0, 0, 284600975549, 474267887240, 83143337836, 1206465782, 0, 0] := by
  decide +kernel

theorem rows6533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6533 = true := by
  decide +kernel

theorem tot6533 : totK PD2M8K2 D2M8K2.t6533 = [0, 163384141823, 424033453517, 303344162769, 33890259123, 0, 0, 0] := by
  decide +kernel

theorem rows6534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6534 = true := by
  decide +kernel

theorem tot6534 : totK PD2M8K2 D2M8K2.t6534 = [0, 172561248214, 487069664998, 229287068746, 11405872210, 0, 0, 0] := by
  decide +kernel

theorem rows6535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6535 = true := by
  decide +kernel

theorem tot6535 : totK PD2M8K2 D2M8K2.t6535 = [0, 182209097136, 463397944625, 234811524247, 15424826760, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
