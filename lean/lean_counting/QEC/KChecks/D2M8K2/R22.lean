import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows88 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t88 = true := by
  decide +kernel

theorem tot88 : totK PD2M8K2 D2M8K2.t88 = [0, 195245184233, 470899040213, 210054480388, 14703944056, 0, 0, 0] := by
  decide +kernel

theorem rows89 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t89 = true := by
  decide +kernel

theorem tot89 : totK PD2M8K2 D2M8K2.t89 = [0, 172757610090, 478599138049, 221537469026, 10794973564, 0, 0, 0] := by
  decide +kernel

theorem rows90 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t90 = true := by
  decide +kernel

theorem tot90 : totK PD2M8K2 D2M8K2.t90 = [0, 86510406232, 357870689092, 355130266956, 66507005035, 1239866073, 0, 0] := by
  decide +kernel

theorem rows91 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t91 = true := by
  decide +kernel

theorem tot91 : totK PD2M8K2 D2M8K2.t91 = [0, 34277757279, 362038796826, 449781122638, 44669065535, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
