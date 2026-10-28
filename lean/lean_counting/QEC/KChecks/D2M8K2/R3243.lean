import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12972 = true := by
  decide +kernel

theorem tot12972 : totK PD2M8K2 D2M8K2.t12972 = [0, 0, 223195761406, 489325856183, 166810049743, 4763850746, 0, 0] := by
  decide +kernel

theorem rows12973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12973 = true := by
  decide +kernel

theorem tot12973 : totK PD2M8K2 D2M8K2.t12973 = [0, 0, 195428235083, 464465232223, 210520059310, 12886858747, 0, 0] := by
  decide +kernel

theorem rows12974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12974 = true := by
  decide +kernel

theorem tot12974 : totK PD2M8K2 D2M8K2.t12974 = [0, 0, 199805085383, 472441208032, 186900241104, 9653832318, 0, 0] := by
  decide +kernel

theorem rows12975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12975 = true := by
  decide +kernel

theorem tot12975 : totK PD2M8K2 D2M8K2.t12975 = [0, 0, 102969198944, 414439589961, 310938977509, 29157609761, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
