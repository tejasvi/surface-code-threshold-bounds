import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2940 = true := by
  decide +kernel

theorem tot2940 : totK PD2M8K2 D2M8K2.t2940 = [157123059778, 450968906585, 280722994032, 23795831542, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2941 = true := by
  decide +kernel

theorem tot2941 : totK PD2M8K2 D2M8K2.t2941 = [0, 221417802542, 492991112333, 162837838786, 7165314891, 0, 0, 0] := by
  decide +kernel

theorem rows2942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2942 = true := by
  decide +kernel

theorem tot2942 : totK PD2M8K2 D2M8K2.t2942 = [67204494367, 302259456096, 390081465544, 116942123189, 5878468449, 0, 0, 0] := by
  decide +kernel

theorem rows2943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2943 = true := by
  decide +kernel

theorem tot2943 : totK PD2M8K2 D2M8K2.t2943 = [173966681360, 456366362082, 272612711157, 27872146588, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
