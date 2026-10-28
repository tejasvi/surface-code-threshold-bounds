import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7616 = true := by
  decide +kernel

theorem tot7616 : totK PD2M8K2 D2M8K2.t7616 = [0, 154963680961, 441848686683, 268290138515, 23217014164, 0, 0, 0] := by
  decide +kernel

theorem rows7617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7617 = true := by
  decide +kernel

theorem tot7617 : totK PD2M8K2 D2M8K2.t7617 = [0, 0, 273511648429, 506487210215, 105480919048, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7618 = true := by
  decide +kernel

theorem tot7618 : totK PD2M8K2 D2M8K2.t7618 = [0, 118631238717, 387816483934, 368379907672, 50005620594, 0, 0, 0] := by
  decide +kernel

theorem rows7619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7619 = true := by
  decide +kernel

theorem tot7619 : totK PD2M8K2 D2M8K2.t7619 = [0, 185700417655, 467203890513, 235523311520, 14894621840, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
