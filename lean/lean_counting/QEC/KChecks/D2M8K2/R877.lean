import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3508 = true := by
  decide +kernel

theorem tot3508 : totK PD2M8K2 D2M8K2.t3508 = [0, 287389604151, 510337938727, 99479559984, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3509 = true := by
  decide +kernel

theorem tot3509 : totK PD2M8K2 D2M8K2.t3509 = [185044317917, 447423014545, 264922915501, 31906536366, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3510 = true := by
  decide +kernel

theorem tot3510 : totK PD2M8K2 D2M8K2.t3510 = [193912918259, 477843477488, 229739708139, 12432084775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3511 = true := by
  decide +kernel

theorem tot3511 : totK PD2M8K2 D2M8K2.t3511 = [37190922132, 282770278736, 391463960971, 186039510693, 21383147344, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
