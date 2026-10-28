import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t772 = true := by
  decide +kernel

theorem tot772 : totK PD2M8K2 D2M8K2.t772 = [0, 55268097201, 342716458225, 411914881505, 73312947221, 1096505104, 0, 0] := by
  decide +kernel

theorem rows773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t773 = true := by
  decide +kernel

theorem tot773 : totK PD2M8K2 D2M8K2.t773 = [0, 36207263364, 283201722883, 455079989279, 109223346689, 3821179711, 0, 0] := by
  decide +kernel

theorem rows774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t774 = true := by
  decide +kernel

theorem tot774 : totK PD2M8K2 D2M8K2.t774 = [0, 199213555022, 461851949764, 225196159709, 19461533568, 0, 0, 0] := by
  decide +kernel

theorem rows775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t775 = true := by
  decide +kernel

theorem tot775 : totK PD2M8K2 D2M8K2.t775 = [0, 179476509406, 473167570588, 236570964257, 13855693431, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
