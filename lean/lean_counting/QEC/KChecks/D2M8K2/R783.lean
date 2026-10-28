import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3132 = true := by
  decide +kernel

theorem tot3132 : totK PD2M8K2 D2M8K2.t3132 = [0, 207044127538, 482220505625, 182751264555, 11643020496, 0, 0, 0] := by
  decide +kernel

theorem rows3133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3133 = true := by
  decide +kernel

theorem tot3133 : totK PD2M8K2 D2M8K2.t3133 = [161066439721, 444305744826, 285214525577, 36984958459, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3134 = true := by
  decide +kernel

theorem tot3134 : totK PD2M8K2 D2M8K2.t3134 = [178297711870, 466966193151, 244215531591, 15534827846, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3135 = true := by
  decide +kernel

theorem tot3135 : totK PD2M8K2 D2M8K2.t3135 = [87521967088, 342180409888, 383300811566, 85424896294, 1197396724, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
