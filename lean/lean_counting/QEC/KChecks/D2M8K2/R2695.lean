import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10780 = true := by
  decide +kernel

theorem tot10780 : totK PD2M8K2 D2M8K2.t10780 = [0, 167856958355, 453189392702, 248345457017, 26887476853, 0, 0, 0] := by
  decide +kernel

theorem rows10781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10781 = true := by
  decide +kernel

theorem tot10781 : totK PD2M8K2 D2M8K2.t10781 = [0, 155717007505, 458732670714, 257435974079, 18721956145, 0, 0, 0] := by
  decide +kernel

theorem rows10782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10782 = true := by
  decide +kernel

theorem tot10782 : totK PD2M8K2 D2M8K2.t10782 = [0, 0, 284743460490, 502515048276, 96464761359, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10783 = true := by
  decide +kernel

theorem tot10783 : totK PD2M8K2 D2M8K2.t10783 = [0, 161042149573, 394694299270, 261701864662, 78809828810, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
