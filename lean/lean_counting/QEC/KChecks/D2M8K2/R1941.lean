import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7764 = true := by
  decide +kernel

theorem tot7764 : totK PD2M8K2 D2M8K2.t7764 = [0, 0, 137060727193, 436399688468, 288636326127, 22932096383, 0, 0] := by
  decide +kernel

theorem rows7765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7765 = true := by
  decide +kernel

theorem tot7765 : totK PD2M8K2 D2M8K2.t7765 = [0, 0, 0, 286828789646, 493958721271, 93382461046, 1369150432, 0] := by
  decide +kernel

theorem rows7766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7766 = true := by
  decide +kernel

theorem tot7766 : totK PD2M8K2 D2M8K2.t7766 = [0, 0, 179655910069, 430668965848, 282224452666, 32672786286, 0, 0] := by
  decide +kernel

theorem rows7767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7767 = true := by
  decide +kernel

theorem tot7767 : totK PD2M8K2 D2M8K2.t7767 = [0, 0, 193225112833, 492861434839, 227682605444, 9527750275, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
