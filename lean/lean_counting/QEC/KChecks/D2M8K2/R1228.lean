import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4912 = true := by
  decide +kernel

theorem tot4912 : totK PD2M8K2 D2M8K2.t4912 = [0, 0, 0, 178857416970, 469030722827, 229914377576, 13810245755, 0] := by
  decide +kernel

theorem rows4913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4913 = true := by
  decide +kernel

theorem tot4913 : totK PD2M8K2 D2M8K2.t4913 = [0, 0, 0, 223190989674, 489572816100, 157453017826, 2601813065, 0] := by
  decide +kernel

theorem rows4914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4914 = true := by
  decide +kernel

theorem tot4914 : totK PD2M8K2 D2M8K2.t4914 = [0, 0, 0, 174699479077, 474832685393, 214789120219, 11981965306, 0] := by
  decide +kernel

theorem rows4915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4915 = true := by
  decide +kernel

theorem tot4915 : totK PD2M8K2 D2M8K2.t4915 = [0, 0, 0, 92049777499, 432950358627, 319679401362, 29931588713, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
