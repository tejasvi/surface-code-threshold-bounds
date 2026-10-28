import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5568 = true := by
  decide +kernel

theorem tot5568 : totK PD2M8K2 D2M8K2.t5568 = [0, 204123096801, 478226660057, 213508975409, 11056080877, 0, 0, 0] := by
  decide +kernel

theorem rows5569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5569 = true := by
  decide +kernel

theorem tot5569 : totK PD2M8K2 D2M8K2.t5569 = [0, 167250329393, 460351972347, 232517998303, 13144444366, 0, 0, 0] := by
  decide +kernel

theorem rows5570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5570 = true := by
  decide +kernel

theorem tot5570 : totK PD2M8K2 D2M8K2.t5570 = [0, 0, 302708854430, 470984023442, 76533227365, 1021600638, 0, 0] := by
  decide +kernel

theorem rows5571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5571 = true := by
  decide +kernel

theorem tot5571 : totK PD2M8K2 D2M8K2.t5571 = [0, 100329972706, 351941051641, 320649090577, 76305736775, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
