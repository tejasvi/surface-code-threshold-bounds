import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9672 = true := by
  decide +kernel

theorem tot9672 : totK PD2M8K2 D2M8K2.t9672 = [0, 103911860836, 330133508975, 317760517195, 132258307366, 8073511420, 0, 0] := by
  decide +kernel

theorem rows9673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9673 = true := by
  decide +kernel

theorem tot9673 : totK PD2M8K2 D2M8K2.t9673 = [0, 171013736089, 436341051729, 276311502258, 29741106488, 0, 0, 0] := by
  decide +kernel

theorem rows9674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9674 = true := by
  decide +kernel

theorem tot9674 : totK PD2M8K2 D2M8K2.t9674 = [0, 151025757301, 452345075539, 281441116881, 23575980931, 0, 0, 0] := by
  decide +kernel

theorem rows9675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9675 = true := by
  decide +kernel

theorem tot9675 : totK PD2M8K2 D2M8K2.t9675 = [0, 0, 217065273577, 494735144719, 168426805967, 7166294683, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
