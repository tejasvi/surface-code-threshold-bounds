import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2888 = true := by
  decide +kernel

theorem tot2888 : totK PD2M8K2 D2M8K2.t2888 = [0, 172972150006, 456955334227, 266807769569, 23282239808, 0, 0, 0] := by
  decide +kernel

theorem rows2889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2889 = true := by
  decide +kernel

theorem tot2889 : totK PD2M8K2 D2M8K2.t2889 = [0, 96020318410, 419973769143, 332130428901, 33989640530, 0, 0, 0] := by
  decide +kernel

theorem rows2890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2890 = true := by
  decide +kernel

theorem tot2890 : totK PD2M8K2 D2M8K2.t2890 = [0, 0, 229828757431, 468515467965, 167503850153, 9579374723, 0, 0] := by
  decide +kernel

theorem rows2891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2891 = true := by
  decide +kernel

theorem tot2891 : totK PD2M8K2 D2M8K2.t2891 = [0, 101139757463, 343909035841, 319419509567, 81446091316, 3436822651, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
