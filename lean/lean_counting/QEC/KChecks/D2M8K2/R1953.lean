import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7812 = true := by
  decide +kernel

theorem tot7812 : totK PD2M8K2 D2M8K2.t7812 = [0, 173140878375, 479095774107, 257833084152, 15195366310, 0, 0, 0] := by
  decide +kernel

theorem rows7813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7813 = true := by
  decide +kernel

theorem tot7813 : totK PD2M8K2 D2M8K2.t7813 = [0, 0, 171170662244, 447119842664, 259489810359, 25373788367, 0, 0] := by
  decide +kernel

theorem rows7814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7814 = true := by
  decide +kernel

theorem tot7814 : totK PD2M8K2 D2M8K2.t7814 = [0, 0, 212634926774, 495723256893, 192962100260, 5430665091, 0, 0] := by
  decide +kernel

theorem rows7815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7815 = true := by
  decide +kernel

theorem tot7815 : totK PD2M8K2 D2M8K2.t7815 = [0, 157736353808, 372632089603, 269154469873, 107213271605, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
