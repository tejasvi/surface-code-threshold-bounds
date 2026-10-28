import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16348 = true := by
  decide +kernel

theorem tot16348 : totK PD2M8K2 D2M8K2.t16348 = [0, 0, 0, 284107023692, 507187829836, 100781713235, 1369150432, 0] := by
  decide +kernel

theorem rows16349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16349 = true := by
  decide +kernel

theorem tot16349 : totK PD2M8K2 D2M8K2.t16349 = [0, 0, 93054923246, 388558673288, 390284898271, 48030406142, 0, 0] := by
  decide +kernel

theorem rows16350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16350 = true := by
  decide +kernel

theorem tot16350 : totK PD2M8K2 D2M8K2.t16350 = [0, 0, 173940095272, 448761472774, 261232326304, 18025429048, 0, 0] := by
  decide +kernel

theorem rows16351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16351 = true := by
  decide +kernel

theorem tot16351 : totK PD2M8K2 D2M8K2.t16351 = [0, 0, 159209688015, 461678385292, 278809162252, 28927609467, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
