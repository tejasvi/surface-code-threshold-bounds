import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2856 = true := by
  decide +kernel

theorem tot2856 : totK PD2M8K2 D2M8K2.t2856 = [0, 66506520845, 320014197774, 413075113421, 94806899959, 1415142070, 0, 0] := by
  decide +kernel

theorem rows2857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2857 = true := by
  decide +kernel

theorem tot2857 : totK PD2M8K2 D2M8K2.t2857 = [0, 177174997332, 456152875370, 266721105315, 27343338882, 0, 0, 0] := by
  decide +kernel

theorem rows2858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2858 = true := by
  decide +kernel

theorem tot2858 : totK PD2M8K2 D2M8K2.t2858 = [0, 172704866115, 470318223261, 258432329070, 14067608542, 0, 0, 0] := by
  decide +kernel

theorem rows2859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2859 = true := by
  decide +kernel

theorem tot2859 : totK PD2M8K2 D2M8K2.t2859 = [0, 0, 290874428655, 486089064204, 116671751058, 1238673482, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
