import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9484 = true := by
  decide +kernel

theorem tot9484 : totK PD2M8K2 D2M8K2.t9484 = [183377369878, 450399732009, 268509242884, 29214137000, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9485 = true := by
  decide +kernel

theorem tot9485 : totK PD2M8K2 D2M8K2.t9485 = [138521910136, 448781206607, 295582835891, 30547516331, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9486 = true := by
  decide +kernel

theorem tot9486 : totK PD2M8K2 D2M8K2.t9486 = [3736707029, 271328803890, 507931545759, 126503554120, 3869034280, 0, 0, 0] := by
  decide +kernel

theorem rows9487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9487 = true := by
  decide +kernel

theorem tot9487 : totK PD2M8K2 D2M8K2.t9487 = [189053791860, 466624110720, 246232801323, 23349548986, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
