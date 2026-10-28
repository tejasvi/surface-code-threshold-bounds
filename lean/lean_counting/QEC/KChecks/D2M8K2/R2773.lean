import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11092 = true := by
  decide +kernel

theorem tot11092 : totK PD2M8K2 D2M8K2.t11092 = [0, 208550078131, 477924247936, 185036500773, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows11093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11093 = true := by
  decide +kernel

theorem tot11093 : totK PD2M8K2 D2M8K2.t11093 = [0, 191179371718, 478834906869, 216036297211, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows11094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11094 = true := by
  decide +kernel

theorem tot11094 : totK PD2M8K2 D2M8K2.t11094 = [0, 196743230454, 469404941391, 206132282026, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows11095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11095 = true := by
  decide +kernel

theorem tot11095 : totK PD2M8K2 D2M8K2.t11095 = [0, 106767371626, 421429965087, 329694562488, 31201891542, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
