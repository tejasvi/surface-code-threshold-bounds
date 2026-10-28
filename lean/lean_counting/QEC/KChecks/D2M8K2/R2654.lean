import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10616 = true := by
  decide +kernel

theorem tot10616 : totK PD2M8K2 D2M8K2.t10616 = [0, 0, 111942245247, 402501180430, 359467329710, 40856537140, 0, 0] := by
  decide +kernel

theorem rows10617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10617 = true := by
  decide +kernel

theorem tot10617 : totK PD2M8K2 D2M8K2.t10617 = [0, 0, 212612633411, 483944356150, 205106234265, 9703098049, 0, 0] := by
  decide +kernel

theorem rows10618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10618 = true := by
  decide +kernel

theorem tot10618 : totK PD2M8K2 D2M8K2.t10618 = [0, 0, 178006553107, 474490327227, 234798013559, 14182039650, 0, 0] := by
  decide +kernel

theorem rows10619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10619 = true := by
  decide +kernel

theorem tot10619 : totK PD2M8K2 D2M8K2.t10619 = [0, 0, 181844105063, 471860801506, 247863058804, 18820204905, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
