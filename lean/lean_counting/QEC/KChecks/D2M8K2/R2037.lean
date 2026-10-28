import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8148 = true := by
  decide +kernel

theorem tot8148 : totK PD2M8K2 D2M8K2.t8148 = [0, 0, 188545087923, 455795281893, 242034754938, 20804897180, 0, 0] := by
  decide +kernel

theorem rows8149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8149 = true := by
  decide +kernel

theorem tot8149 : totK PD2M8K2 D2M8K2.t8149 = [0, 0, 197984017368, 488568111033, 210826682654, 9901604992, 0, 0] := by
  decide +kernel

theorem rows8150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8150 = true := by
  decide +kernel

theorem tot8150 : totK PD2M8K2 D2M8K2.t8150 = [0, 156102866075, 363995845248, 231414067994, 118852353352, 13566920432, 0, 0] := by
  decide +kernel

theorem rows8151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8151 = true := by
  decide +kernel

theorem tot8151 : totK PD2M8K2 D2M8K2.t8151 = [0, 186128966495, 471976278624, 218993481040, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
