import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6548 = true := by
  decide +kernel

theorem tot6548 : totK PD2M8K2 D2M8K2.t6548 = [40482760351, 346630445703, 461341805328, 59309331295, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6549 = true := by
  decide +kernel

theorem tot6549 : totK PD2M8K2 D2M8K2.t6549 = [184520668900, 448101612164, 263817007022, 29130330491, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6550 = true := by
  decide +kernel

theorem tot6550 : totK PD2M8K2 D2M8K2.t6550 = [178333478127, 483541599350, 234491589432, 12432084775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6551 = true := by
  decide +kernel

theorem tot6551 : totK PD2M8K2 D2M8K2.t6551 = [0, 215858473472, 458192976321, 217035133753, 21383147344, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
