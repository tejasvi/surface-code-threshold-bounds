import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4 = true := by
  decide +kernel

theorem tot4 : totK PD2M8K2 D2M8K2.t4 = [196096843738, 471802910198, 228390613243, 18034991674, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5 = true := by
  decide +kernel

theorem tot5 : totK PD2M8K2 D2M8K2.t5 = [172549945486, 460857571778, 244422470035, 13632511348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6 = true := by
  decide +kernel

theorem tot6 : totK PD2M8K2 D2M8K2.t6 = [0, 284488617163, 501159035451, 108573990309, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows7 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7 = true := by
  decide +kernel

theorem tot7 : totK PD2M8K2 D2M8K2.t7 = [7266429264, 190861156283, 469816747580, 191393467800, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
