import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15836 = true := by
  decide +kernel

theorem tot15836 : totK PD2M8K2 D2M8K2.t15836 = [0, 0, 89648888184, 269153403972, 377434001940, 161713434429, 7877424857, 0] := by
  decide +kernel

theorem rows15837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15837 = true := by
  decide +kernel

theorem tot15837 : totK PD2M8K2 D2M8K2.t15837 = [0, 0, 156171804027, 452113635197, 281780805064, 28950172052, 0, 0] := by
  decide +kernel

theorem rows15838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15838 = true := by
  decide +kernel

theorem tot15838 : totK PD2M8K2 D2M8K2.t15838 = [0, 0, 85009007106, 397802875812, 394067726810, 51152309797, 0, 0] := by
  decide +kernel

theorem rows15839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15839 = true := by
  decide +kernel

theorem tot15839 : totK PD2M8K2 D2M8K2.t15839 = [0, 0, 70006874778, 341592825446, 397431194793, 79812918356, 1547833102, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
