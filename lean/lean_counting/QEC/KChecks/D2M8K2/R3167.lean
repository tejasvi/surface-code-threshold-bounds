import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12668 = true := by
  decide +kernel

theorem tot12668 : totK PD2M8K2 D2M8K2.t12668 = [0, 0, 0, 283009383550, 507827851362, 90840794409, 1096505104, 0] := by
  decide +kernel

theorem rows12669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12669 = true := by
  decide +kernel

theorem tot12669 : totK PD2M8K2 D2M8K2.t12669 = [0, 0, 150612604471, 364863862650, 282932328400, 81516442103, 3820764243, 0] := by
  decide +kernel

theorem rows12670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12670 = true := by
  decide +kernel

theorem tot12670 : totK PD2M8K2 D2M8K2.t12670 = [0, 0, 210489031472, 460267992653, 222710680162, 15590341496, 0, 0] := by
  decide +kernel

theorem rows12671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12671 = true := by
  decide +kernel

theorem tot12671 : totK PD2M8K2 D2M8K2.t12671 = [0, 0, 177688991163, 475211339045, 224857782471, 11683647270, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
