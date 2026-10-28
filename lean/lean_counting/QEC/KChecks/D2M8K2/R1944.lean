import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7776 = true := by
  decide +kernel

theorem tot7776 : totK PD2M8K2 D2M8K2.t7776 = [0, 0, 177564626352, 460241368433, 263836609277, 23481379564, 0, 0] := by
  decide +kernel

theorem rows7777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7777 = true := by
  decide +kernel

theorem tot7777 : totK PD2M8K2 D2M8K2.t7777 = [0, 0, 176973689601, 468324918114, 254054485716, 13874960422, 0, 0] := by
  decide +kernel

theorem rows7778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7778 = true := by
  decide +kernel

theorem tot7778 : totK PD2M8K2 D2M8K2.t7778 = [0, 0, 0, 276502075076, 511845463716, 112154557169, 1268739303, 0] := by
  decide +kernel

theorem rows7779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7779 = true := by
  decide +kernel

theorem tot7779 : totK PD2M8K2 D2M8K2.t7779 = [0, 55649345463, 68083696581, 180717196959, 399244916212, 180682077367, 12680714061, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
