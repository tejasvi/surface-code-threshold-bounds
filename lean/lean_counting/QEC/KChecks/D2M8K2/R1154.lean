import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4616 = true := by
  decide +kernel

theorem tot4616 : totK PD2M8K2 D2M8K2.t4616 = [0, 0, 173052895926, 470859108431, 259525811433, 18549410704, 0, 0] := by
  decide +kernel

theorem rows4617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4617 = true := by
  decide +kernel

theorem tot4617 : totK PD2M8K2 D2M8K2.t4617 = [0, 0, 87646833503, 414182932344, 372308218478, 33493311700, 0, 0] := by
  decide +kernel

theorem rows4618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4618 = true := by
  decide +kernel

theorem tot4618 : totK PD2M8K2 D2M8K2.t4618 = [0, 0, 82963577057, 343411323548, 377602209119, 79922212771, 1334898114, 0] := by
  decide +kernel

theorem rows4619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4619 = true := by
  decide +kernel

theorem tot4619 : totK PD2M8K2 D2M8K2.t4619 = [0, 0, 176836871606, 445419424933, 267734809207, 28356147231, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
