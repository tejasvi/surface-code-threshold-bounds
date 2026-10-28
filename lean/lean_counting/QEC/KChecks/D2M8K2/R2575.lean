import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10300 = true := by
  decide +kernel

theorem tot10300 : totK PD2M8K2 D2M8K2.t10300 = [0, 183213899372, 431500844917, 204784150754, 47643630897, 8677971875, 0, 0] := by
  decide +kernel

theorem rows10301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10301 = true := by
  decide +kernel

theorem tot10301 : totK PD2M8K2 D2M8K2.t10301 = [0, 190310960992, 475444709055, 219769563352, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows10302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10302 = true := by
  decide +kernel

theorem tot10302 : totK PD2M8K2 D2M8K2.t10302 = [0, 32681031224, 295889738101, 439947960611, 98861813508, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10303 = true := by
  decide +kernel

theorem tot10303 : totK PD2M8K2 D2M8K2.t10303 = [0, 92925902623, 384638580971, 398411539596, 44649318683, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
