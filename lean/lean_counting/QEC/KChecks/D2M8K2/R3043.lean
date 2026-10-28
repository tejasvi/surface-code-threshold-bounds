import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12172 = true := by
  decide +kernel

theorem tot12172 : totK PD2M8K2 D2M8K2.t12172 = [98665772061, 404950551889, 365659817903, 40257877305, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12173 = true := by
  decide +kernel

theorem tot12173 : totK PD2M8K2 D2M8K2.t12173 = [183473870801, 445699654589, 253294313299, 25853288521, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12174 = true := by
  decide +kernel

theorem tot12174 : totK PD2M8K2 D2M8K2.t12174 = [128474520331, 428961228693, 299181807103, 24860381427, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12175 = true := by
  decide +kernel

theorem tot12175 : totK PD2M8K2 D2M8K2.t12175 = [0, 200615714129, 489089279011, 183092072639, 9587713104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
