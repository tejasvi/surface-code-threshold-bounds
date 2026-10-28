import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11152 = true := by
  decide +kernel

theorem tot11152 : totK PD2M8K2 D2M8K2.t11152 = [0, 190074907532, 457351330407, 242256838017, 21085133815, 0, 0, 0] := by
  decide +kernel

theorem rows11153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11153 = true := by
  decide +kernel

theorem tot11153 : totK PD2M8K2 D2M8K2.t11153 = [0, 195185206634, 462331264833, 219719984547, 17028109311, 0, 0, 0] := by
  decide +kernel

theorem rows11154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11154 = true := by
  decide +kernel

theorem tot11154 : totK PD2M8K2 D2M8K2.t11154 = [0, 0, 313163477732, 487136213337, 84911994950, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11155 = true := by
  decide +kernel

theorem tot11155 : totK PD2M8K2 D2M8K2.t11155 = [0, 84566615325, 311440983316, 386428879344, 97384188329, 3820764243, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
