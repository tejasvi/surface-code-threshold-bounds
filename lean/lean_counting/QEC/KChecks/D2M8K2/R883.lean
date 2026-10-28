import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3532 = true := by
  decide +kernel

theorem tot3532 : totK PD2M8K2 D2M8K2.t3532 = [0, 195501500900, 476195169608, 218344877436, 12439805748, 0, 0, 0] := by
  decide +kernel

theorem rows3533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3533 = true := by
  decide +kernel

theorem tot3533 : totK PD2M8K2 D2M8K2.t3533 = [0, 8125304319, 309813089016, 463277926870, 89061600175, 1171084559, 0, 0] := by
  decide +kernel

theorem rows3534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3534 = true := by
  decide +kernel

theorem tot3534 : totK PD2M8K2 D2M8K2.t3534 = [0, 0, 201912566502, 454237263100, 184286511780, 11934365838, 0, 0] := by
  decide +kernel

theorem rows3535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3535 = true := by
  decide +kernel

theorem tot3535 : totK PD2M8K2 D2M8K2.t3535 = [0, 176997651882, 454436668748, 249305721419, 18466753785, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
