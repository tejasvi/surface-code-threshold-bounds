import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2264 = true := by
  decide +kernel

theorem tot2264 : totK PD2M8K2 D2M8K2.t2264 = [0, 0, 171963229968, 464568448252, 234184105377, 13597322258, 0, 0] := by
  decide +kernel

theorem rows2265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2265 = true := by
  decide +kernel

theorem tot2265 : totK PD2M8K2 D2M8K2.t2265 = [0, 0, 173975553048, 466066529458, 228720599028, 17078533784, 0, 0] := by
  decide +kernel

theorem rows2266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2266 = true := by
  decide +kernel

theorem tot2266 : totK PD2M8K2 D2M8K2.t2266 = [0, 0, 175152473654, 451569638804, 245032019639, 16584918422, 0, 0] := by
  decide +kernel

theorem rows2267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2267 = true := by
  decide +kernel

theorem tot2267 : totK PD2M8K2 D2M8K2.t2267 = [0, 0, 92671400364, 368369816129, 343609321090, 66055548425, 1095107716, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
