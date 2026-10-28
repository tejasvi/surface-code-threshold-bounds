import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11392 = true := by
  decide +kernel

theorem tot11392 : totK PD2M8K2 D2M8K2.t11392 = [0, 0, 176412919510, 448713560927, 254441325245, 25373788367, 0, 0] := by
  decide +kernel

theorem rows11393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11393 = true := by
  decide +kernel

theorem tot11393 : totK PD2M8K2 D2M8K2.t11393 = [0, 0, 209408415894, 497579372369, 195215875531, 5430665091, 0, 0] := by
  decide +kernel

theorem rows11394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11394 = true := by
  decide +kernel

theorem tot11394 : totK PD2M8K2 D2M8K2.t11394 = [0, 156443567796, 376451861378, 258182744029, 109364689035, 6804944647, 0, 0] := by
  decide +kernel

theorem rows11395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11395 = true := by
  decide +kernel

theorem tot11395 : totK PD2M8K2 D2M8K2.t11395 = [0, 177805552528, 447194903028, 257704640388, 21094945499, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
