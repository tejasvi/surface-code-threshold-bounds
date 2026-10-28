import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9144 = true := by
  decide +kernel

theorem tot9144 : totK PD2M8K2 D2M8K2.t9144 = [0, 180614463113, 468740436242, 251854298523, 22776889198, 0, 0, 0] := by
  decide +kernel

theorem rows9145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9145 = true := by
  decide +kernel

theorem tot9145 : totK PD2M8K2 D2M8K2.t9145 = [0, 160952786184, 469442303089, 258293261902, 14661804167, 0, 0, 0] := by
  decide +kernel

theorem rows9146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9146 = true := by
  decide +kernel

theorem tot9146 : totK PD2M8K2 D2M8K2.t9146 = [0, 0, 278262188298, 501340415425, 115666258792, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9147 = true := by
  decide +kernel

theorem tot9147 : totK PD2M8K2 D2M8K2.t9147 = [0, 18567060971, 210101834414, 449854476786, 190828975181, 11985024718, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
