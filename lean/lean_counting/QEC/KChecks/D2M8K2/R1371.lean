import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5484 = true := by
  decide +kernel

theorem tot5484 : totK PD2M8K2 D2M8K2.t5484 = [0, 0, 11859818758, 304460189536, 478409047749, 94519633759, 1198073392, 0] := by
  decide +kernel

theorem rows5485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5485 = true := by
  decide +kernel

theorem tot5485 : totK PD2M8K2 D2M8K2.t5485 = [0, 0, 3757402556, 222367702695, 491693389222, 160940525282, 5346271539, 0] := by
  decide +kernel

theorem rows5486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5486 = true := by
  decide +kernel

theorem tot5486 : totK PD2M8K2 D2M8K2.t5486 = [0, 0, 189350654926, 465310119738, 244421200237, 22631808637, 0, 0] := by
  decide +kernel

theorem rows5487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5487 = true := by
  decide +kernel

theorem tot5487 : totK PD2M8K2 D2M8K2.t5487 = [0, 0, 192630085063, 470295951662, 233790517897, 15296801605, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
