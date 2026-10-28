import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16012 = true := by
  decide +kernel

theorem tot16012 : totK PD2M8K2 D2M8K2.t16012 = [0, 0, 182137505762, 480838819948, 247544682450, 13849458279, 0, 0] := by
  decide +kernel

theorem rows16013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16013 = true := by
  decide +kernel

theorem tot16013 : totK PD2M8K2 D2M8K2.t16013 = [0, 0, 0, 275531576931, 497331399343, 107696409226, 1268739303, 0] := by
  decide +kernel

theorem rows16014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16014 = true := by
  decide +kernel

theorem tot16014 : totK PD2M8K2 D2M8K2.t16014 = [0, 0, 0, 180734381033, 493682942879, 194510783826, 6799393473, 0] := by
  decide +kernel

theorem rows16015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16015 = true := by
  decide +kernel

theorem tot16015 : totK PD2M8K2 D2M8K2.t16015 = [0, 0, 0, 196424319065, 468515727143, 179243741001, 11549710348, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
