import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7476 = true := by
  decide +kernel

theorem tot7476 : totK PD2M8K2 D2M8K2.t7476 = [0, 195487222018, 486440940709, 211461599656, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows7477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7477 = true := by
  decide +kernel

theorem tot7477 : totK PD2M8K2 D2M8K2.t7477 = [0, 198525938337, 465862187922, 213423807362, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows7478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7478 = true := by
  decide +kernel

theorem tot7478 : totK PD2M8K2 D2M8K2.t7478 = [0, 4188399740, 303356170046, 485094842282, 105513768865, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7479 = true := by
  decide +kernel

theorem tot7479 : totK PD2M8K2 D2M8K2.t7479 = [0, 87704378323, 370521140583, 402610798089, 49162413314, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
