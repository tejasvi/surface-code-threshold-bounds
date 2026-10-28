import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3804 = true := by
  decide +kernel

theorem tot3804 : totK PD2M8K2 D2M8K2.t3804 = [0, 196397146471, 477886357149, 194573324637, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows3805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3805 = true := by
  decide +kernel

theorem tot3805 : totK PD2M8K2 D2M8K2.t3805 = [152574673325, 441598444832, 296920823652, 35795845360, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3806 = true := by
  decide +kernel

theorem tot3806 : totK PD2M8K2 D2M8K2.t3806 = [174773797690, 467861520869, 244891237509, 16818232580, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3807 = true := by
  decide +kernel

theorem tot3807 : totK PD2M8K2 D2M8K2.t3807 = [0, 287629322928, 513262647172, 101440160231, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
