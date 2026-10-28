import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4116 = true := by
  decide +kernel

theorem tot4116 : totK PD2M8K2 D2M8K2.t4116 = [0, 0, 177775196140, 464969553209, 244796297693, 16565187625, 0, 0] := by
  decide +kernel

theorem rows4117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4117 = true := by
  decide +kernel

theorem tot4117 : totK PD2M8K2 D2M8K2.t4117 = [0, 0, 189698427269, 465405413885, 234819040023, 19920018668, 0, 0] := by
  decide +kernel

theorem rows4118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4118 = true := by
  decide +kernel

theorem tot4118 : totK PD2M8K2 D2M8K2.t4118 = [0, 0, 190584896806, 477161462476, 224439569318, 12439805748, 0, 0] := by
  decide +kernel

theorem rows4119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4119 = true := by
  decide +kernel

theorem tot4119 : totK PD2M8K2 D2M8K2.t4119 = [0, 0, 52277709162, 340427931931, 426206535004, 67828314025, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
