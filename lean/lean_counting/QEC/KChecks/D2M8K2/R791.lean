import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3164 = true := by
  decide +kernel

theorem tot3164 : totK PD2M8K2 D2M8K2.t3164 = [0, 0, 226119444592, 509120568738, 153043832979, 2484078857, 0, 0] := by
  decide +kernel

theorem rows3165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3165 = true := by
  decide +kernel

theorem tot3165 : totK PD2M8K2 D2M8K2.t3165 = [157459612076, 362140913955, 148522860641, 97927807795, 88350200022, 6818291842, 0, 0] := by
  decide +kernel

theorem rows3166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3166 = true := by
  decide +kernel

theorem tot3166 : totK PD2M8K2 D2M8K2.t3166 = [187603789923, 478523584820, 223251958860, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3167 = true := by
  decide +kernel

theorem tot3167 : totK PD2M8K2 D2M8K2.t3167 = [52501347129, 309721539842, 412028383360, 93321622391, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
