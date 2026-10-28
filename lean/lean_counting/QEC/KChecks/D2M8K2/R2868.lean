import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11472 = true := by
  decide +kernel

theorem tot11472 : totK PD2M8K2 D2M8K2.t11472 = [0, 180284548937, 455083156778, 258828572078, 18405470726, 0, 0, 0] := by
  decide +kernel

theorem rows11473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11473 = true := by
  decide +kernel

theorem tot11473 : totK PD2M8K2 D2M8K2.t11473 = [0, 86696072139, 345611996878, 368555132748, 76693146098, 1178750802, 0, 0] := by
  decide +kernel

theorem rows11474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11474 = true := by
  decide +kernel

theorem tot11474 : totK PD2M8K2 D2M8K2.t11474 = [0, 0, 263713034796, 484345843663, 152806217405, 8470662040, 0, 0] := by
  decide +kernel

theorem rows11475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11475 = true := by
  decide +kernel

theorem tot11475 : totK PD2M8K2 D2M8K2.t11475 = [0, 121014833368, 340899337056, 318023445207, 88755029350, 3546687146, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
