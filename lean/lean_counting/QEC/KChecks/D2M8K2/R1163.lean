import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4652 = true := by
  decide +kernel

theorem tot4652 : totK PD2M8K2 D2M8K2.t4652 = [0, 172522672634, 451159843906, 246375458197, 18197172049, 0, 0, 0] := by
  decide +kernel

theorem rows4653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4653 = true := by
  decide +kernel

theorem tot4653 : totK PD2M8K2 D2M8K2.t4653 = [0, 86397487671, 375477696202, 357289568992, 69280135418, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4654 = true := by
  decide +kernel

theorem tot4654 : totK PD2M8K2 D2M8K2.t4654 = [0, 0, 307882049004, 514578169281, 76919210215, 0, 0, 0] := by
  decide +kernel

theorem rows4655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4655 = true := by
  decide +kernel

theorem tot4655 : totK PD2M8K2 D2M8K2.t4655 = [0, 178109623265, 450623316397, 257874356489, 28594709391, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
