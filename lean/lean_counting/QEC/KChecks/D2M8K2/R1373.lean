import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5492 = true := by
  decide +kernel

theorem tot5492 : totK PD2M8K2 D2M8K2.t5492 = [0, 0, 0, 192127022050, 479886769570, 235492833521, 16488343163, 0] := by
  decide +kernel

theorem rows5493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5493 = true := by
  decide +kernel

theorem tot5493 : totK PD2M8K2 D2M8K2.t5493 = [0, 0, 0, 225712329567, 490664779566, 171963746199, 5264096131, 0] := by
  decide +kernel

theorem rows5494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5494 = true := by
  decide +kernel

theorem tot5494 : totK PD2M8K2 D2M8K2.t5494 = [0, 0, 0, 203251151421, 469338736700, 203625553594, 12845077926, 0] := by
  decide +kernel

theorem rows5495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5495 = true := by
  decide +kernel

theorem tot5495 : totK PD2M8K2 D2M8K2.t5495 = [0, 0, 0, 187477474026, 453104265330, 225118520341, 15438353713, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
