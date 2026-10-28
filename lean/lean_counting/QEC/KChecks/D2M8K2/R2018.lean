import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8072 = true := by
  decide +kernel

theorem tot8072 : totK PD2M8K2 D2M8K2.t8072 = [0, 0, 213999433187, 492535008982, 175749831787, 5351797944, 0, 0] := by
  decide +kernel

theorem rows8073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8073 = true := by
  decide +kernel

theorem tot8073 : totK PD2M8K2 D2M8K2.t8073 = [0, 0, 173549263906, 475260166767, 227587416568, 11326869986, 0, 0] := by
  decide +kernel

theorem rows8074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8074 = true := by
  decide +kernel

theorem tot8074 : totK PD2M8K2 D2M8K2.t8074 = [0, 0, 175444743614, 469097365254, 211937287205, 12284330786, 0, 0] := by
  decide +kernel

theorem rows8075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8075 = true := by
  decide +kernel

theorem tot8075 : totK PD2M8K2 D2M8K2.t8075 = [0, 0, 206120861572, 475543453305, 207721074934, 8394630506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
