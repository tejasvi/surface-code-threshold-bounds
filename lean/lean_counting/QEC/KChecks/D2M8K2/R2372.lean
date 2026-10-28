import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9488 = true := by
  decide +kernel

theorem tot9488 : totK PD2M8K2 D2M8K2.t9488 = [192915914892, 459020673307, 232420767871, 15950928196, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9489 = true := by
  decide +kernel

theorem tot9489 : totK PD2M8K2 D2M8K2.t9489 = [38140235179, 330939384238, 440635672482, 97098050980, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows9490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9490 = true := by
  decide +kernel

theorem tot9490 : totK PD2M8K2 D2M8K2.t9490 = [0, 207726175175, 473644766931, 181076361789, 7430810494, 0, 0, 0] := by
  decide +kernel

theorem rows9491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9491 = true := by
  decide +kernel

theorem tot9491 : totK PD2M8K2 D2M8K2.t9491 = [0, 150519354518, 438237241460, 298563759993, 32129844625, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
