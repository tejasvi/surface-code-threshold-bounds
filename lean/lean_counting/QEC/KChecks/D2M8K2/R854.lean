import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3416 = true := by
  decide +kernel

theorem tot3416 : totK PD2M8K2 D2M8K2.t3416 = [159457644122, 433118636173, 261986858870, 54537438563, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows3417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3417 = true := by
  decide +kernel

theorem tot3417 : totK PD2M8K2 D2M8K2.t3417 = [171422536039, 445207833986, 257322435450, 16833795729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3418 = true := by
  decide +kernel

theorem tot3418 : totK PD2M8K2 D2M8K2.t3418 = [91637619653, 365022729093, 361918286104, 67101242570, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3419 = true := by
  decide +kernel

theorem tot3419 : totK PD2M8K2 D2M8K2.t3419 = [0, 316017510347, 513503966815, 79502354213, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
