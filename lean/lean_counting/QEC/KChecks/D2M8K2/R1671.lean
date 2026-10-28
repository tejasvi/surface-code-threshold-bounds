import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6684 = true := by
  decide +kernel

theorem tot6684 : totK PD2M8K2 D2M8K2.t6684 = [0, 67167979029, 246298388468, 410280165449, 169858241548, 5411637735, 0, 0] := by
  decide +kernel

theorem rows6685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6685 = true := by
  decide +kernel

theorem tot6685 : totK PD2M8K2 D2M8K2.t6685 = [0, 179491162942, 465682424316, 248514036717, 22640061284, 0, 0, 0] := by
  decide +kernel

theorem rows6686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6686 = true := by
  decide +kernel

theorem tot6686 : totK PD2M8K2 D2M8K2.t6686 = [0, 178660293291, 475769697203, 236147173001, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows6687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6687 = true := by
  decide +kernel

theorem tot6687 : totK PD2M8K2 D2M8K2.t6687 = [0, 0, 281651037411, 499291217782, 110104931667, 1178750802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
