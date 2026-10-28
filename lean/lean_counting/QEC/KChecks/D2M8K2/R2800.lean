import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11200 = true := by
  decide +kernel

theorem tot11200 : totK PD2M8K2 D2M8K2.t11200 = [0, 0, 288040014298, 503234909640, 100693958116, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11201 = true := by
  decide +kernel

theorem tot11201 : totK PD2M8K2 D2M8K2.t11201 = [0, 157922964993, 433096736304, 285146003050, 32666639443, 0, 0, 0] := by
  decide +kernel

theorem rows11202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11202 = true := by
  decide +kernel

theorem tot11202 : totK PD2M8K2 D2M8K2.t11202 = [0, 208009014103, 464851563326, 206587246055, 12293048165, 0, 0, 0] := by
  decide +kernel

theorem rows11203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11203 = true := by
  decide +kernel

theorem tot11203 : totK PD2M8K2 D2M8K2.t11203 = [0, 34274186757, 322952733028, 448293870380, 91579856950, 1129969115, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
