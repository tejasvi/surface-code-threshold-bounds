import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1360 = true := by
  decide +kernel

theorem tot1360 : totK PD2M8K2 D2M8K2.t1360 = [0, 87204366028, 342459425070, 377584196067, 90129587710, 2896345377, 0, 0] := by
  decide +kernel

theorem rows1361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1361 = true := by
  decide +kernel

theorem tot1361 : totK PD2M8K2 D2M8K2.t1361 = [0, 159633350406, 444435075601, 267153138579, 26680464437, 0, 0, 0] := by
  decide +kernel

theorem rows1362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1362 = true := by
  decide +kernel

theorem tot1362 : totK PD2M8K2 D2M8K2.t1362 = [0, 166086246454, 449129045974, 259999302196, 18799705882, 0, 0, 0] := by
  decide +kernel

theorem rows1363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1363 = true := by
  decide +kernel

theorem tot1363 : totK PD2M8K2 D2M8K2.t1363 = [0, 0, 218459988615, 494357126267, 161417290565, 5228939780, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
