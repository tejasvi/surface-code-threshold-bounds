import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t584 = true := by
  decide +kernel

theorem tot584 : totK PD2M8K2 D2M8K2.t584 = [0, 196243988229, 475596078646, 231110699255, 13428733938, 0, 0, 0] := by
  decide +kernel

theorem rows585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t585 = true := by
  decide +kernel

theorem tot585 : totK PD2M8K2 D2M8K2.t585 = [0, 0, 289894806027, 489868851913, 110265034575, 1268739303, 0, 0] := by
  decide +kernel

theorem rows586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t586 = true := by
  decide +kernel

theorem tot586 : totK PD2M8K2 D2M8K2.t586 = [0, 0, 208573723174, 483835910455, 183504120634, 7375673972, 0, 0] := by
  decide +kernel

theorem rows587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t587 = true := by
  decide +kernel

theorem tot587 : totK PD2M8K2 D2M8K2.t587 = [157204742844, 327477144452, 135904263732, 153593468391, 117449145188, 13338039113, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
