import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12984 = true := by
  decide +kernel

theorem tot12984 : totK PD2M8K2 D2M8K2.t12984 = [0, 0, 190645847162, 467196869559, 237612050211, 18252358503, 0, 0] := by
  decide +kernel

theorem rows12985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12985 = true := by
  decide +kernel

theorem tot12985 : totK PD2M8K2 D2M8K2.t12985 = [0, 0, 124063894021, 433748957174, 286830270824, 20119444901, 0, 0] := by
  decide +kernel

theorem rows12986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12986 = true := by
  decide +kernel

theorem tot12986 : totK PD2M8K2 D2M8K2.t12986 = [0, 0, 0, 318337960599, 461678681238, 77727178394, 1021600638, 0] := by
  decide +kernel

theorem rows12987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12987 = true := by
  decide +kernel

theorem tot12987 : totK PD2M8K2 D2M8K2.t12987 = [0, 0, 170308802673, 386843710656, 241705245970, 67645321355, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
