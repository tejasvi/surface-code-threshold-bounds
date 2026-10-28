import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5716 = true := by
  decide +kernel

theorem tot5716 : totK PD2M8K2 D2M8K2.t5716 = [0, 134704392973, 368104727571, 304548289647, 74741004326, 3462014130, 0, 0] := by
  decide +kernel

theorem rows5717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5717 = true := by
  decide +kernel

theorem tot5717 : totK PD2M8K2 D2M8K2.t5717 = [0, 175950133931, 446516568951, 260705020214, 28219134086, 0, 0, 0] := by
  decide +kernel

theorem rows5718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5718 = true := by
  decide +kernel

theorem tot5718 : totK PD2M8K2 D2M8K2.t5718 = [0, 94402016517, 397622112848, 328151917513, 47508632949, 1096505104, 0, 0] := by
  decide +kernel

theorem rows5719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5719 = true := by
  decide +kernel

theorem tot5719 : totK PD2M8K2 D2M8K2.t5719 = [0, 0, 300483015702, 524796281764, 76873245017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
