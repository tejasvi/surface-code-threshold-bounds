import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15808 = true := by
  decide +kernel

theorem tot15808 : totK PD2M8K2 D2M8K2.t15808 = [0, 0, 193096509388, 498125560089, 192988345485, 3921178515, 0, 0] := by
  decide +kernel

theorem rows15809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15809 = true := by
  decide +kernel

theorem tot15809 : totK PD2M8K2 D2M8K2.t15809 = [0, 0, 189239385722, 466426644046, 203539941838, 12403393969, 0, 0] := by
  decide +kernel

theorem rows15810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15810 = true := by
  decide +kernel

theorem tot15810 : totK PD2M8K2 D2M8K2.t15810 = [0, 0, 168186701097, 482569374914, 243704812481, 10591053842, 0, 0] := by
  decide +kernel

theorem rows15811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15811 = true := by
  decide +kernel

theorem tot15811 : totK PD2M8K2 D2M8K2.t15811 = [0, 0, 179247117373, 470425638018, 237290786950, 12029765029, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
