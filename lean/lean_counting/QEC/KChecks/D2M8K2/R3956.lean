import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15824 = true := by
  decide +kernel

theorem tot15824 : totK PD2M8K2 D2M8K2.t15824 = [0, 141351442391, 423501035221, 318611013238, 43406092933, 0, 0, 0] := by
  decide +kernel

theorem rows15825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15825 = true := by
  decide +kernel

theorem tot15825 : totK PD2M8K2 D2M8K2.t15825 = [0, 193524230942, 460759573941, 240611558266, 18158528194, 0, 0, 0] := by
  decide +kernel

theorem rows15826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15826 = true := by
  decide +kernel

theorem tot15826 : totK PD2M8K2 D2M8K2.t15826 = [0, 43743759897, 388280990375, 426335296924, 50985045085, 0, 0, 0] := by
  decide +kernel

theorem rows15827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15827 = true := by
  decide +kernel

theorem tot15827 : totK PD2M8K2 D2M8K2.t15827 = [0, 68495116861, 326354069859, 400188374215, 101675968182, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
