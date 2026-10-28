import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5576 = true := by
  decide +kernel

theorem tot5576 : totK PD2M8K2 D2M8K2.t5576 = [0, 273154203640, 507118762002, 113302438727, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5577 = true := by
  decide +kernel

theorem tot5577 : totK PD2M8K2 D2M8K2.t5577 = [86950764009, 400840562638, 374190849187, 40339252501, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5578 = true := by
  decide +kernel

theorem tot5578 : totK PD2M8K2 D2M8K2.t5578 = [179317979831, 451314299861, 261980923167, 27531060247, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5579 = true := by
  decide +kernel

theorem tot5579 : totK PD2M8K2 D2M8K2.t5579 = [155214850970, 447435643933, 271321749068, 19872456436, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
