import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8 = true := by
  decide +kernel

theorem tot8 : totK PD2M8K2 D2M8K2.t8 = [204114858079, 471944878221, 222359245342, 18043869161, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9 = true := by
  decide +kernel

theorem tot9 : totK PD2M8K2 D2M8K2.t9 = [189964607396, 465744288169, 224204172210, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10 = true := by
  decide +kernel

theorem tot10 : totK PD2M8K2 D2M8K2.t10 = [19358310964, 304091931287, 474397728017, 99389764021, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11 = true := by
  decide +kernel

theorem tot11 : totK PD2M8K2 D2M8K2.t11 = [0, 192715700272, 463287335801, 198742889533, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
