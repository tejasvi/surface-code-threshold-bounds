import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2984 = true := by
  decide +kernel

theorem tot2984 : totK PD2M8K2 D2M8K2.t2984 = [0, 0, 220402426981, 480186999330, 157679288499, 4944878611, 0, 0] := by
  decide +kernel

theorem rows2985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2985 = true := by
  decide +kernel

theorem tot2985 : totK PD2M8K2 D2M8K2.t2985 = [0, 0, 19319729168, 313623752998, 428082561271, 81613890576, 1275377855, 0] := by
  decide +kernel

theorem rows2986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2986 = true := by
  decide +kernel

theorem tot2986 : totK PD2M8K2 D2M8K2.t2986 = [0, 0, 105208279033, 432082967129, 294842884207, 21372115616, 0, 0] := by
  decide +kernel

theorem rows2987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2987 = true := by
  decide +kernel

theorem tot2987 : totK PD2M8K2 D2M8K2.t2987 = [0, 0, 197646064584, 469146608168, 210944432716, 12552144954, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
